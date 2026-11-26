/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import TimedKt.RunLib
import Mathlib.Data.Sign.Defs

/-!
# Constant-Cost Codes for Turing-Machine Data Structures

The pieces of the Turing-machine simulation of `TimedKt.TMSim` that do not mention a machine:
fixed `Nat.Partrec.Code`s that update an encoded input zipper, an encoded work tape and an
encoded output buffer, each within a constant number of `Run` transitions.

## Encodings

* A **work tape** is `pair Ls Rs` of two pair stacks (`RunLib.pairStack`) of cell codes
  (`0` blank, `1` false, `2` true): `Rs` holds the cell under the head and those to its right,
  `Ls` those to its left, nearest first. Popping the empty stack `0` yields `0`, the blank, so the
  blank infinite tails are implicit.
* The **input tape** is a zipper over the virtual word `frame p ++ y`, which is never written out:
  its unvisited suffix is produced on demand from the list encodings of `p` and `y` by a
  three-mode generator (`TMCode.genList`), so the input arrives in the form the universal machine
  supplies it, `encode (p, y)`, and costs nothing before it is read. Cells already visited are kept
  in two pair stacks of codes `1`/`2` (`0` marks the empty stack).
* The **output** is a pair stack of the output bits in reverse order together with its length.

Reading the generator needs the head, tail and nil test of Mathlib's list encoding, which cost
`O(1)` transitions (`TimedKt.list_destruct_const`).

## Main results

* `TMCode.genPop_spec`, `TMCode.popR_spec`: one generator / right-side pop in `O(1)` transitions.
* `TMCode.zmove_spec`: one input-head move in `O(1)` transitions.
* `TMCode.tapeUpd_spec`, `TMCode.wupd_spec`, `TMCode.syms_spec`: one work-tape action, all `k`
  work-tape actions, and reading the `k` work-tape symbols, in `O(1)` transitions (for fixed `k`).
* `TMCode.oupd_spec`: appending at most one output symbol in `O(1)` transitions.
-/

open Nat.Partrec Nat

namespace TimedKt

namespace TMCode

open ListDestruct RunLib

/-! ### Projection paths -/

/-- Apply `left` (`false`) or `right` (`true`) in the listed order. -/
def pth : List Bool → Code
  | [] => Code.id
  | b :: bs => .comp (pth bs) (if b then .right else .left)

/-- The value of a projection path. -/
def pathVal : List Bool → ℕ → ℕ
  | [], n => n
  | b :: bs, n => pathVal bs (if b then n.unpair.2 else n.unpair.1)

@[simp] theorem pathVal_nil (n : ℕ) : pathVal [] n = n := rfl

@[simp] theorem pathVal_cons_false (bs : List Bool) (a b : ℕ) :
    pathVal (false :: bs) (Nat.pair a b) = pathVal bs a := by
  simp [pathVal]

@[simp] theorem pathVal_cons_true (bs : List Bool) (a b : ℕ) :
    pathVal (true :: bs) (Nat.pair a b) = pathVal bs b := by
  simp [pathVal]

@[simp] theorem pathVal_single_false (n : ℕ) : pathVal [false] n = n.unpair.1 := rfl

@[simp] theorem pathVal_single_true (n : ℕ) : pathVal [true] n = n.unpair.2 := rfl

@[simp] theorem pathVal_zero : ∀ bs : List Bool, pathVal bs 0 = 0
  | [] => rfl
  | b :: bs => by cases b <;> simpa [pathVal, unpair_zero'] using pathVal_zero bs

theorem pth_spec : ∀ (bs : List Bool) (n : ℕ), RunsLe (pth bs) n (pathVal bs n) (2 * bs.length + 3)
  | [], n => runsLe_id n
  | b :: bs, n => by
      have hb : RunsLe (if b then Code.right else Code.left) n
          (if b then n.unpair.2 else n.unpair.1) 1 := by
        cases b
        · exact runsLe_left n
        · exact runsLe_right n
      have := hb.comp (pth_spec bs _)
      refine this.of_eq ?_ (by simp only [List.length_cons]; omega)
      cases b <;> rfl

/-! ### Cell codes and list encodings -/

/-- Code of an input bit: `false ↦ 1`, `true ↦ 2` (nonzero, so `0` marks an empty stack). -/
def bcode (b : Bool) : ℕ := Encodable.encode b + 1

theorem bcode_false : bcode false = 1 := rfl
theorem bcode_true : bcode true = 2 := rfl

/-- Decode a nonzero cell code (`2 ↦ true`, otherwise `false`). -/
def bdec (n : ℕ) : Bool := n == 2

@[simp] theorem bdec_bcode (b : Bool) : bdec (bcode b) = b := by cases b <;> rfl

theorem bcode_le_two (b : Bool) : bcode b ≤ 2 := by cases b <;> simp [bcode_false, bcode_true]

theorem one_le_bcode (b : Bool) : 1 ≤ bcode b := by cases b <;> simp [bcode_false, bcode_true]

/-- The pair stack of the codes of a bit list. -/
def bstk (l : List Bool) : ℕ := pairStack (l.map bcode)

@[simp] theorem bstk_nil : bstk [] = 0 := rfl

@[simp] theorem bstk_cons (b : Bool) (l : List Bool) :
    bstk (b :: l) = Nat.pair (bcode b) (bstk l) := rfl

/-- The list encoding as a natural number. -/
abbrev enc (l : List Bool) : ℕ := Encodable.encode l

/-! ### The input generator

The unvisited suffix of the input word `frame p ++ y` is produced from a mode and the remaining
parts of `p` and `y`:

* mode `0`: the remaining word is `frame P ++ Y`;
* mode `1`: the marker of the head of `P` has been produced; the remaining word is
  `P.headD false :: (frame P.tail ++ Y)`;
* mode `2`: the remaining word is `Y`. -/

/-- The word still to be produced by the generator. -/
def genList (md : ℕ) (P Y : List Bool) : List Bool :=
  match md with
  | 0 => P.flatMap (fun b => [true, b]) ++ [false] ++ Y
  | 1 => P.headD false :: (P.tail.flatMap (fun b => [true, b]) ++ [false] ++ Y)
  | _ => Y

/-- The encoded generator state. -/
def encG (md : ℕ) (P Y : List Bool) : ℕ := Nat.pair md (Nat.pair (enc P) (enc Y))

/-- One generator step: the produced cell code (`0` at the end of the word) and the new state. -/
def genPop : ℕ → List Bool → List Bool → ℕ × ℕ × List Bool × List Bool
  | 0, [], Y => (1, 2, [], Y)
  | 0, b :: P, Y => (2, 1, b :: P, Y)
  | 1, P, Y => (bcode (P.headD false), 0, P.tail, Y)
  | _, P, [] => (0, 2, P, [])
  | _, P, b :: Y => (bcode b, 2, P, Y)

/-- Encoded result of a generator step. -/
def encGP (r : ℕ × ℕ × List Bool × List Bool) : ℕ := Nat.pair r.1 (encG r.2.1 r.2.2.1 r.2.2.2)

theorem genPop_md_le (md : ℕ) (P Y : List Bool) : (genPop md P Y).2.1 ≤ 2 := by
  unfold genPop
  split <;> simp

/-- The generator produces its word cell by cell, and `0` once the word is exhausted. -/
theorem genPop_correct {md : ℕ} (hmd : md ≤ 2) (P Y : List Bool) :
    (genList md P Y = [] → (genPop md P Y).1 = 0 ∧
        genList (genPop md P Y).2.1 (genPop md P Y).2.2.1 (genPop md P Y).2.2.2 = []) ∧
    ∀ b rest, genList md P Y = b :: rest → (genPop md P Y).1 = bcode b ∧
        genList (genPop md P Y).2.1 (genPop md P Y).2.2.1 (genPop md P Y).2.2.2 = rest := by
  rcases (by omega : md = 0 ∨ md = 1 ∨ md = 2) with rfl | rfl | rfl
  · cases P with
    | nil => simp [genList, genPop, bcode]
    | cons b P => simp [genList, genPop, bcode]
  · cases P with
    | nil => simp [genList, genPop]
    | cons b P => simp [genList, genPop]
  · cases Y with
    | nil => simp [genList, genPop]
    | cons b Y => simp [genList, genPop]

/-- Nil test, head code and tail on the list encoding, as named codes. -/
def hdCode : Code := .comp .succ headCode

theorem hd_spec (l : List Bool) : RunsLe hdCode (enc l) (bcode (l.headD false)) 121 :=
  ((head_runsLe l).comp (runsLe_succ _)).mono (by norm_num)

theorem nn_spec (l : List Bool) : RunsLe nonNilCode (enc l) (if l = [] then 0 else 1) 120 :=
  (nonNil_runsLe l).mono (by norm_num)

theorem tl_spec (l : List Bool) : RunsLe tailCode (enc l) (enc l.tail) 163 := tail_runsLe l

/-- The generator step as a code on `encG md P Y`. -/
def genPopCode : Code :=
  mux [mux [.pair (Code.const 1) (.pair (Code.const 2) .right),
            .pair (Code.const 2) (.pair (Code.const 1) .right)]
         (.comp nonNilCode (pth [true, false])),
       .pair (.comp hdCode (pth [true, false]))
         (.pair .zero (.pair (.comp tailCode (pth [true, false])) (pth [true, true]))),
       mux [.pair .zero Code.id,
            .pair (.comp hdCode (pth [true, true]))
              (.pair (Code.const 2)
                (.pair (pth [true, false]) (.comp tailCode (pth [true, true]))))]
         (.comp nonNilCode (pth [true, true]))]
    .left

theorem genPop_spec : ∃ B, ∀ md P Y, md ≤ 2 →
    RunsLe genPopCode (encG md P Y) (encGP (genPop md P Y)) B := by
  refine ⟨5000, fun md P Y hmd => ?_⟩
  have hp1 := pth_spec [true, false] (encG md P Y)
  have hp2 := pth_spec [true, true] (encG md P Y)
  simp only [encG, pathVal_cons_true, pathVal_cons_false, pathVal_nil, List.length_cons,
    List.length_nil] at hp1 hp2
  have hR := runsLe_right (encG md P Y)
  simp only [encG, Nat.unpair_pair] at hR
  -- the candidates of mode 0
  have c00 := (runsLe_const 1 (encG md P Y)).pair ((runsLe_const 2 (encG md P Y)).pair hR)
  have c01 := (runsLe_const 2 (encG md P Y)).pair ((runsLe_const 1 (encG md P Y)).pair hR)
  have s0 := hp1.comp (nn_spec P)
  have m0 := mux_spec' (ws := [Nat.pair 1 (Nat.pair 2 (Nat.pair (enc P) (enc Y))),
      Nat.pair 2 (Nat.pair 1 (Nat.pair (enc P) (enc Y)))]) s0
    (List.Forall₂.cons c00 (List.Forall₂.cons c01 List.Forall₂.nil)) (by split <;> simp)
  -- the candidate of mode 1
  have c1 := (hp1.comp (hd_spec P)).pair ((runsLe_zero (encG md P Y)).pair
    ((hp1.comp (tl_spec P)).pair hp2))
  -- the candidates of mode 2
  have c20 := (runsLe_zero (encG md P Y)).pair (runsLe_id (encG md P Y))
  have c21 := (hp2.comp (hd_spec Y)).pair ((runsLe_const 2 (encG md P Y)).pair
    (hp1.pair (hp2.comp (tl_spec Y))))
  have s2 := hp2.comp (nn_spec Y)
  have m2 := mux_spec' (ws := [Nat.pair 0 (encG md P Y),
      Nat.pair (bcode (Y.headD false)) (Nat.pair 2 (Nat.pair (enc P) (enc Y.tail)))]) s2
    (List.Forall₂.cons (c20.mono (by norm_num : _ ≤ 400))
      (List.Forall₂.cons (c21.mono (by norm_num : _ ≤ 400)) List.Forall₂.nil))
    (by split <;> simp)
  have sel := runsLe_left (encG md P Y)
  simp only [encG, Nat.unpair_pair] at sel
  have top := mux_spec' (ws := [_, _, _]) sel
    (List.Forall₂.cons (m0.mono (by norm_num : _ ≤ 1500))
      (List.Forall₂.cons (c1.mono (by norm_num : _ ≤ 1500))
        (List.Forall₂.cons (m2.mono (by norm_num : _ ≤ 1500)) List.Forall₂.nil)))
    (by simp; omega)
  refine top.of_eq ?_ (by norm_num)
  rcases (by omega : md = 0 ∨ md = 1 ∨ md = 2) with rfl | rfl | rfl
  · cases P <;> simp [genPop, encGP, encG]
  · simp [genPop, encGP, encG]
  · cases Y <;> simp [genPop, encGP, encG]

/-! ### Popping the right side of the input zipper

The right side is `pair (bstk Rb) G`: cells pushed back by left moves, then the generator. -/

/-- The encoded right side. -/
def encRS (Rb : List Bool) (md : ℕ) (P Y : List Bool) : ℕ := Nat.pair (bstk Rb) (encG md P Y)

/-- Pop the right side: the produced cell code and the new pushed-back list and generator. -/
def popR : List Bool → ℕ → List Bool → List Bool → ℕ × List Bool × ℕ × List Bool × List Bool
  | b :: Rb, md, P, Y => (bcode b, Rb, md, P, Y)
  | [], md, P, Y => ((genPop md P Y).1, [], (genPop md P Y).2.1, (genPop md P Y).2.2.1,
      (genPop md P Y).2.2.2)

/-- Encoded result of a pop. -/
def encPR (r : ℕ × List Bool × ℕ × List Bool × List Bool) : ℕ :=
  Nat.pair r.1 (encRS r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2)

theorem popR_md_le {Rb : List Bool} {md : ℕ} (hmd : md ≤ 2) (P Y : List Bool) :
    (popR Rb md P Y).2.2.1 ≤ 2 := by
  cases Rb with
  | nil => exact genPop_md_le md P Y
  | cons b Rb => exact hmd

/-- Popping the right side produces the next cell of `Rb ++ genList`, or `0` at its end. -/
theorem popR_correct {md : ℕ} (hmd : md ≤ 2) (Rb P Y : List Bool) :
    let r := popR Rb md P Y
    (Rb ++ genList md P Y = [] → r.1 = 0 ∧ r.2.1 ++ genList r.2.2.1 r.2.2.2.1 r.2.2.2.2 = []) ∧
    ∀ b rest, Rb ++ genList md P Y = b :: rest →
      r.1 = bcode b ∧ r.2.1 ++ genList r.2.2.1 r.2.2.2.1 r.2.2.2.2 = rest := by
  cases Rb with
  | cons c Rb =>
      refine ⟨fun h => by simp at h, fun b rest h => ?_⟩
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩
  | nil =>
      have := genPop_correct hmd P Y
      simpa [popR] using this

/-- The right-side pop as a code on `encRS Rb md P Y`. -/
def popRCode : Code :=
  mux [.comp (.pair (pth [true, false]) (.pair .left (pth [true, true])))
         (.pair .left (.comp genPopCode .right)),
       .pair (pth [false, false]) (.pair (pth [false, true]) .right),
       .pair (pth [false, false]) (.pair (pth [false, true]) .right)]
    (pth [false, false])

theorem popR_spec : ∃ B, ∀ Rb md P Y, md ≤ 2 →
    RunsLe popRCode (encRS Rb md P Y) (encPR (popR Rb md P Y)) B := by
  obtain ⟨Bg, hg⟩ := genPop_spec
  refine ⟨3 * Bg + 300, fun Rb md P Y hmd => ?_⟩
  have hpLL := pth_spec [false, false] (encRS Rb md P Y)
  have hpLR := pth_spec [false, true] (encRS Rb md P Y)
  have hpR : RunsLe .right (encRS Rb md P Y) (encG md P Y) 1 := by
    simpa [encRS] using runsLe_right (encRS Rb md P Y)
  have hpL : RunsLe .left (encRS Rb md P Y) (bstk Rb) 1 := by
    simpa [encRS] using runsLe_left (encRS Rb md P Y)
  have cN := hpLL.pair (hpLR.pair hpR)
  have hin := hpL.pair (hpR.comp (hg md P Y hmd))
  have hout := (pth_spec [true, false] (Nat.pair (bstk Rb) (encGP (genPop md P Y)))).pair
    ((runsLe_left (Nat.pair (bstk Rb) (encGP (genPop md P Y)))).pair
      (pth_spec [true, true] (Nat.pair (bstk Rb) (encGP (genPop md P Y)))))
  have cE := hin.comp hout
  simp only [encGP, pathVal_cons_true, pathVal_cons_false, pathVal_nil, Nat.unpair_pair,
    List.length_cons, List.length_nil] at cE
  have hall := fa3 (cE.mono (by omega : _ ≤ Bg + 40))
    (cN.mono (by simp only [List.length_cons, List.length_nil]; omega : _ ≤ Bg + 40))
    (cN.mono (by simp only [List.length_cons, List.length_nil]; omega : _ ≤ Bg + 40))
  cases Rb with
  | nil =>
      have hsel := hpLL
      have hv : pathVal [false, false] (encRS [] md P Y) = 0 := by simp [encRS]
      rw [hv] at hsel
      have := mux_spec' hsel hall (by simp)
      refine this.of_eq ?_ (by simp only [List.length_cons, List.length_nil]; omega)
      simp [popR, encPR, encRS]
  | cons b Rb =>
      have hsel := hpLL
      have hv : pathVal [false, false] (encRS (b :: Rb) md P Y) = bcode b := by simp [encRS]
      rw [hv] at hsel
      have := mux_spec' hsel hall (by have := bcode_le_two b; simp; omega)
      refine this.of_eq ?_ (by simp only [List.length_cons, List.length_nil]; omega)
      have h1 := one_le_bcode b
      have h2 := bcode_le_two b
      rcases (by omega : bcode b = 1 ∨ bcode b = 2) with h | h <;>
        simp [h, popR, encPR, encRS]

/-! ### The input zipper -/

/-- The input zipper: the code `H` of the cell under the head (`0` the right boundary blank,
`1`/`2` an input bit, `3` the left boundary blank), the input cells left of the head (nearest
first), the pushed-back cells right of the head, and the generator for the rest. -/
structure Zip where
  /-- Code of the cell under the head. -/
  H : ℕ
  /-- Input cells left of the head, nearest first. -/
  Ls : List Bool
  /-- Pushed-back input cells right of the head, nearest first. -/
  Rb : List Bool
  /-- Generator mode. -/
  md : ℕ
  /-- Generator: remaining program bits. -/
  P : List Bool
  /-- Generator: remaining condition bits. -/
  Y : List Bool

/-- The encoded zipper. -/
def Zip.enc (z : Zip) : ℕ := Nat.pair z.H (Nat.pair (bstk z.Ls) (encRS z.Rb z.md z.P z.Y))

/-- Pop the left side: the new head code (`3` at the left boundary) and the remaining cells. -/
def popL : List Bool → ℕ × List Bool
  | [] => (3, [])
  | b :: Ls => (bcode b, Ls)

/-- Move the head right (no move on the right boundary blank). -/
def Zip.moveR (z : Zip) : Zip :=
  if z.H = 0 then z else
    let r := popR z.Rb z.md z.P z.Y
    ⟨r.1, if z.H = 3 then z.Ls else bdec z.H :: z.Ls, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2⟩

/-- Move the head left (no move on the left boundary blank). -/
def Zip.moveL (z : Zip) : Zip :=
  if z.H = 3 then z else
    ⟨(popL z.Ls).1, (popL z.Ls).2, if z.H = 0 then z.Rb else bdec z.H :: z.Rb, z.md, z.P, z.Y⟩

/-- Code of a head movement: `-1 ↦ 0`, `0 ↦ 1`, `+1 ↦ 2`. -/
def mvCode : SignType → ℕ
  | .neg => 0
  | .zero => 1
  | .pos => 2

theorem mvCode_le_two (m : SignType) : mvCode m ≤ 2 := by cases m <;> decide

/-- Move the head as directed. -/
def Zip.move (z : Zip) : SignType → Zip
  | .neg => z.moveL
  | .zero => z
  | .pos => z.moveR

theorem Zip.moveR_md_le {z : Zip} (h : z.md ≤ 2) : z.moveR.md ≤ 2 := by
  unfold Zip.moveR
  split
  · exact h
  · exact popR_md_le h _ _

theorem Zip.move_md_le {z : Zip} (h : z.md ≤ 2) (m : SignType) : (z.move m).md ≤ 2 := by
  cases m with
  | zero => exact h
  | neg => change z.moveL.md ≤ 2; unfold Zip.moveL; split <;> exact h
  | pos => exact Zip.moveR_md_le h

/-- The right move on the encoded zipper. -/
def zRZ : Code :=
  mux [Code.id,
       .comp (.pair (pth [true, false])
           (.pair (.pair (pth [false, false]) (pth [false, true, false])) (pth [true, true])))
         (.pair Code.id (.comp popRCode (pth [true, true]))),
       .comp (.pair (pth [true, false])
           (.pair (.pair (pth [false, false]) (pth [false, true, false])) (pth [true, true])))
         (.pair Code.id (.comp popRCode (pth [true, true]))),
       .comp (.pair (pth [true, false]) (.pair (pth [false, true, false]) (pth [true, true])))
         (.pair Code.id (.comp popRCode (pth [true, true])))]
    .left

theorem zRZ_spec : ∃ B, ∀ z : Zip, z.md ≤ 2 → z.H ≤ 3 → RunsLe zRZ z.enc z.moveR.enc B := by
  obtain ⟨Bp, hp⟩ := popR_spec
  refine ⟨4 * Bp + 400, fun z hmd hH => ?_⟩
  have hR := pth_spec [true, true] z.enc
  simp only [Zip.enc, pathVal_cons_true, pathVal_nil] at hR
  have hin := (runsLe_id z.enc).pair (hR.comp (hp z.Rb z.md z.P z.Y hmd))
  set r := popR z.Rb z.md z.P z.Y with hr
  have h12 := hin.comp ((pth_spec [true, false] _).pair (((pth_spec [false, false] _).pair
    (pth_spec [false, true, false] _)).pair (pth_spec [true, true] _)))
  have h3 := hin.comp ((pth_spec [true, false] _).pair ((pth_spec [false, true, false] _).pair
    (pth_spec [true, true] _)))
  simp only [encPR, Zip.enc, pathVal_cons_true, pathVal_cons_false, pathVal_nil,
    List.length_cons, List.length_nil] at h12 h3
  have hall := fa4 ((runsLe_id z.enc).mono (by omega : 3 ≤ Bp + 60)) (h12.mono (by omega))
    (h12.mono (by omega)) (h3.mono (by omega))
  have hsel : RunsLe .left z.enc z.H 1 := by simpa [Zip.enc] using runsLe_left z.enc
  have := mux_spec' hsel hall (by simp; omega)
  refine this.of_eq ?_ (by simp only [List.length_cons, List.length_nil]; omega)
  rcases (by omega : z.H = 0 ∨ z.H = 1 ∨ z.H = 2 ∨ z.H = 3) with h | h | h | h
  · simp [h, Zip.moveR]
  · simp [h, Zip.moveR, Zip.enc, hr, bdec, bcode_false]
  · simp [h, Zip.moveR, Zip.enc, hr, bdec, bcode_true]
  · simp [h, Zip.moveR, Zip.enc, hr]

/-- The new head code after popping the left side. -/
def hLCode : Code :=
  mux [Code.const 3, pth [true, false, false], pth [true, false, false]] (pth [true, false, false])

/-- The left move on the encoded zipper. -/
def zLZ : Code :=
  mux [.pair hLCode (.pair (pth [true, false, true]) (pth [true, true])),
       .pair hLCode (.pair (pth [true, false, true])
         (.pair (.pair .left (pth [true, true, false])) (pth [true, true, true]))),
       .pair hLCode (.pair (pth [true, false, true])
         (.pair (.pair .left (pth [true, true, false])) (pth [true, true, true]))),
       Code.id]
    .left

theorem pathVal_bstk_left (l : List Bool) :
    (bstk l).unpair.1 = (popL l).1 % 3 := by
  cases l with
  | nil => rfl
  | cons b l =>
      have := bcode_le_two b
      simp only [bstk_cons, Nat.unpair_pair, popL]
      omega

theorem zLZ_spec : ∃ B, ∀ z : Zip, z.H ≤ 3 → RunsLe zLZ z.enc z.moveL.enc B := by
  refine ⟨1000, fun z hH => ?_⟩
  have hc := pth_spec [true, false, false] z.enc
  simp only [Zip.enc, encRS, pathVal_cons_true, pathVal_cons_false,
    List.length_cons, List.length_nil] at hc
  have hhL : RunsLe hLCode z.enc (popL z.Ls).1 100 := by
    have hall := fa3 ((runsLe_const 3 z.enc).mono (by norm_num : 7 ≤ 10)) (hc.mono (by norm_num))
      (hc.mono (by norm_num))
    have hlt : (bstk z.Ls).unpair.1 < 3 := by
      rw [pathVal_bstk_left]; exact Nat.mod_lt _ (by norm_num)
    have := mux_spec' hc hall (by simpa using hlt)
    refine this.of_eq ?_ (by norm_num)
    cases hz : z.Ls with
    | nil => simp [popL]
    | cons b l =>
        have h1 := one_le_bcode b
        have h2 := bcode_le_two b
        rcases (by omega : bcode b = 1 ∨ bcode b = 2) with h | h <;> simp [h, popL]
  have hp1 := pth_spec [true, false, true] z.enc
  have hp2 := pth_spec [true, true] z.enc
  have hp3 := pth_spec [true, true, false] z.enc
  have hp4 := pth_spec [true, true, true] z.enc
  have hl := runsLe_left z.enc
  simp only [Zip.enc, encRS, pathVal_cons_true, pathVal_cons_false, pathVal_nil,
    List.length_cons, List.length_nil, Nat.unpair_pair] at hp1 hp2 hp3 hp4 hl
  have c0 := hhL.pair (hp1.pair hp2)
  have c12 := hhL.pair (hp1.pair ((hl.pair hp3).pair hp4))
  have hall := fa4 (c0.mono (by omega : _ ≤ 200)) (c12.mono (by omega)) (c12.mono (by omega))
    ((runsLe_id z.enc).mono (by omega))
  have hsel : RunsLe .left z.enc z.H 1 := by simpa [Zip.enc] using runsLe_left z.enc
  have := mux_spec' hsel hall (by simp; omega)
  refine this.of_eq ?_ (by simp only [List.length_cons, List.length_nil]; omega)
  have hLs : (bstk z.Ls).unpair.2 = bstk (popL z.Ls).2 := by
    cases z.Ls <;> simp [popL]
  rcases (by omega : z.H = 0 ∨ z.H = 1 ∨ z.H = 2 ∨ z.H = 3) with h | h | h | h
  · simp [h, Zip.moveL, Zip.enc, encRS, hLs]
  · simp [h, Zip.moveL, Zip.enc, encRS, hLs, bdec, bcode_false]
  · simp [h, Zip.moveL, Zip.enc, encRS, hLs, bdec, bcode_true]
  · simp [h, Zip.moveL]

/-- One input-head move, on `pair (encoded zipper) (mvCode m)`. -/
def zmoveCode : Code :=
  mux [.comp zLZ .left, .left, .comp zRZ .left] .right

theorem zmove_spec : ∃ B, ∀ (z : Zip) (m : SignType), z.md ≤ 2 → z.H ≤ 3 →
    RunsLe zmoveCode (Nat.pair z.enc (mvCode m)) (z.move m).enc B := by
  obtain ⟨BR, hR⟩ := zRZ_spec
  obtain ⟨BL, hL⟩ := zLZ_spec
  refine ⟨3 * (BR + BL + 3) + 40, fun z m hmd hH => ?_⟩
  have hl : RunsLe .left (Nat.pair z.enc (mvCode m)) z.enc 1 := by
    simpa using runsLe_left (Nat.pair z.enc (mvCode m))
  have hr : RunsLe .right (Nat.pair z.enc (mvCode m)) (mvCode m) 1 := by
    simpa using runsLe_right (Nat.pair z.enc (mvCode m))
  have hall := fa3 ((hl.comp (hL z hH)).mono (by omega : _ ≤ BR + BL + 3))
    (hl.mono (by omega)) ((hl.comp (hR z hmd hH)).mono (by omega))
  have := mux_spec' hr hall (by have := mvCode_le_two m; simp; omega)
  refine this.of_eq ?_ (by simp only [List.length_cons, List.length_nil]; omega)
  cases m <;> rfl

/-! ### Work tapes -/

/-- One work-tape action on the encoded tape `T = pair Ls Rs` with the encoded action
`wa = pair ws wm` (`ws`: `0` no write, `s + 1` write the cell code `s`; `wm`: `mvCode`). -/
def tapeUpdN (T wa : ℕ) : ℕ :=
  let Ls := T.unpair.1
  let Rs := T.unpair.2
  let s' := [Rs.unpair.1, 0, 1, 2].getD wa.unpair.1 0
  let R1 := Nat.pair s' Rs.unpair.2
  [Nat.pair Ls.unpair.2 (Nat.pair Ls.unpair.1 R1), Nat.pair Ls R1,
    Nat.pair (Nat.pair s' Ls) Rs.unpair.2].getD wa.unpair.2 0

/-- The written cell code. -/
def sNewCode : Code :=
  mux [pth [false, true, false], Code.const 0, Code.const 1, Code.const 2] (pth [true, false])

/-- One work-tape action, on `pair T wa`. -/
def tapeUpdCode : Code :=
  mux [.pair (pth [false, false, true]) (.pair (pth [false, false, false])
          (.pair sNewCode (pth [false, true, true]))),
       .pair (pth [false, false]) (.pair sNewCode (pth [false, true, true])),
       .pair (.pair sNewCode (pth [false, false])) (pth [false, true, true])]
    (pth [true, true])

theorem tapeUpd_spec : ∃ B, ∀ T wa : ℕ, wa.unpair.1 ≤ 3 → wa.unpair.2 ≤ 2 →
    RunsLe tapeUpdCode (Nat.pair T wa) (tapeUpdN T wa) B := by
  refine ⟨1000, fun T wa hws hwm => ?_⟩
  have p := fun bs => pth_spec bs (Nat.pair T wa)
  have hs : RunsLe sNewCode (Nat.pair T wa) ([T.unpair.2.unpair.1, 0, 1, 2].getD wa.unpair.1 0)
      100 := by
    have hall := fa4 ((p [false, true, false]).mono (by simp : _ ≤ 10))
      ((runsLe_const 0 _).mono (by norm_num)) ((runsLe_const 1 _).mono (by norm_num))
      ((runsLe_const 2 _).mono (by norm_num))
    have := mux_spec' (p [true, false]) hall (by simp [pathVal]; omega)
    exact this.of_eq (by simp [pathVal]) (by simp)
  have c0 := (p [false, false, true]).pair ((p [false, false, false]).pair
    (hs.pair (p [false, true, true])))
  have c1 := (p [false, false]).pair (hs.pair (p [false, true, true]))
  have c2 := (hs.pair (p [false, false])).pair (p [false, true, true])
  have hall := fa3 (c0.mono (by simp : _ ≤ 200)) (c1.mono (by simp)) (c2.mono (by simp))
  have := mux_spec' (p [true, true]) hall (by simp [pathVal]; omega)
  refine this.of_eq ?_ (by simp)
  simp [pathVal, tapeUpdN]

/-- The `k`-fold right-nested pair of a family, ending in `0`. -/
def wenc : (k : ℕ) → (Fin k → ℕ) → ℕ
  | 0, _ => 0
  | k + 1, f => Nat.pair (f 0) (wenc k (fun i => f i.succ))

theorem sget_wenc : ∀ (k : ℕ) (f : Fin k → ℕ) (i : Fin k), sget (wenc k f) i = f i
  | 0, _, i => i.elim0
  | k + 1, f, i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [wenc]
      · simp only [wenc, Fin.val_succ, sget_pair_succ]
        exact sget_wenc k _ j

theorem wenc_zero : ∀ k : ℕ, wenc k (fun _ => 0) = 0
  | 0 => rfl
  | k + 1 => by
      change Nat.pair 0 (wenc k (fun _ => 0)) = 0
      rw [wenc_zero k]
      rfl

/-- All `k` work-tape actions, on `pair W WA`. -/
def wupdCode : ℕ → Code
  | 0 => .zero
  | k + 1 => .pair (.comp tapeUpdCode (.pair (pth [false, false]) (pth [true, false])))
      (.comp (wupdCode k) (.pair (pth [false, true]) (pth [true, true])))

theorem wupd_spec : ∀ k : ℕ, ∃ B, ∀ Ts As : Fin k → ℕ,
    (∀ i, (As i).unpair.1 ≤ 3 ∧ (As i).unpair.2 ≤ 2) →
    RunsLe (wupdCode k) (Nat.pair (wenc k Ts) (wenc k As))
      (wenc k (fun i => tapeUpdN (Ts i) (As i))) B
  | 0 => ⟨1, fun _ _ _ => by simpa [wupdCode, wenc] using runsLe_zero _⟩
  | k + 1 => by
      obtain ⟨Bt, ht⟩ := tapeUpd_spec
      obtain ⟨Bk, hk⟩ := wupd_spec k
      refine ⟨Bt + Bk + 100, fun Ts As hA => ?_⟩
      have e : Nat.pair (wenc (k + 1) Ts) (wenc (k + 1) As) = Nat.pair
          (Nat.pair (Ts 0) (wenc k (fun i => Ts i.succ)))
          (Nat.pair (As 0) (wenc k (fun i => As i.succ))) := rfl
      rw [e]
      have p1 := pth_spec [false, false] (Nat.pair
          (Nat.pair (Ts 0) (wenc k (fun i => Ts i.succ)))
          (Nat.pair (As 0) (wenc k (fun i => As i.succ))))
      have p2 := pth_spec [true, false] (Nat.pair
          (Nat.pair (Ts 0) (wenc k (fun i => Ts i.succ)))
          (Nat.pair (As 0) (wenc k (fun i => As i.succ))))
      have p3 := pth_spec [false, true] (Nat.pair
          (Nat.pair (Ts 0) (wenc k (fun i => Ts i.succ)))
          (Nat.pair (As 0) (wenc k (fun i => As i.succ))))
      have p4 := pth_spec [true, true] (Nat.pair
          (Nat.pair (Ts 0) (wenc k (fun i => Ts i.succ)))
          (Nat.pair (As 0) (wenc k (fun i => As i.succ))))
      simp only [pathVal_cons_true, pathVal_cons_false, pathVal_nil, List.length_cons,
        List.length_nil] at p1 p2 p3 p4
      have h0 := (p1.pair p2).comp (ht (Ts 0) (As 0) (hA 0).1 (hA 0).2)
      have h1 := (p3.pair p4).comp
        (hk (fun i => Ts i.succ) (fun i => As i.succ) (fun i => hA i.succ))
      exact (h0.pair h1).mono (by omega)

/-- The `k` work-tape symbols, on `W`. -/
def symsCode : ℕ → Code
  | 0 => .zero
  | k + 1 => .pair (pth [false, true, false]) (.comp (symsCode k) .right)

theorem syms_spec : ∀ k : ℕ, ∃ B, ∀ Ts : Fin k → ℕ,
    RunsLe (symsCode k) (wenc k Ts) (wenc k (fun i => (Ts i).unpair.2.unpair.1)) B
  | 0 => ⟨1, fun _ => by simpa [symsCode, wenc] using runsLe_zero _⟩
  | k + 1 => by
      obtain ⟨Bk, hk⟩ := syms_spec k
      refine ⟨Bk + 20, fun Ts => ?_⟩
      have e : wenc (k + 1) Ts = Nat.pair (Ts 0) (wenc k (fun i => Ts i.succ)) := rfl
      rw [e]
      have h0 := pth_spec [false, true, false] (Nat.pair (Ts 0) (wenc k (fun i => Ts i.succ)))
      have hr := runsLe_right (Nat.pair (Ts 0) (wenc k (fun i => Ts i.succ)))
      simp only [pathVal_cons_false,
        Nat.unpair_pair, List.length_cons, List.length_nil] at h0 hr
      have := h0.pair (hr.comp (hk (fun i => Ts i.succ)))
      exact this.mono (by omega)

/-! ### Output -/

/-- Append at most one output bit to `OP = pair O n` (`os`: `0` none, `encode b + 1` the bit
`b`); `O` is the pair stack of the output bits in reverse order and `n` its length. -/
def oupdN (OP os : ℕ) : ℕ :=
  [OP, Nat.pair (Nat.pair 0 OP.unpair.1) (OP.unpair.2 + 1),
    Nat.pair (Nat.pair 1 OP.unpair.1) (OP.unpair.2 + 1)].getD os 0

/-- The output update, on `pair OP os`. -/
def oupdCode : Code :=
  mux [.left, .pair (.pair .zero (pth [false, false])) (.comp .succ (pth [false, true])),
       .pair (.pair one (pth [false, false])) (.comp .succ (pth [false, true]))] .right

theorem oupd_spec : ∃ B, ∀ OP os : ℕ, os ≤ 2 →
    RunsLe oupdCode (Nat.pair OP os) (oupdN OP os) B := by
  refine ⟨200, fun OP os hos => ?_⟩
  have p1 := pth_spec [false, false] (Nat.pair OP os)
  have p2 := pth_spec [false, true] (Nat.pair OP os)
  simp only [pathVal_cons_false, pathVal_single_false, pathVal_single_true, List.length_cons,
    List.length_nil] at p1 p2
  have hl : RunsLe .left (Nat.pair OP os) OP 1 := by simpa using runsLe_left (Nat.pair OP os)
  have hr : RunsLe .right (Nat.pair OP os) os 1 := by simpa using runsLe_right (Nat.pair OP os)
  have c1 := ((runsLe_zero _).pair p1).pair (p2.comp (runsLe_succ _))
  have c2 := ((runsLe_one _).pair p1).pair (p2.comp (runsLe_succ _))
  have hall := fa3 (hl.mono (by norm_num : 1 ≤ 30)) (c1.mono (by norm_num))
    (c2.mono (by norm_num))
  have := mux_spec' hr hall (by simp; omega)
  exact this.mono (by simp)

/-! ### One step from a decoded action

An encoded configuration is `pair q (pair Zn (pair W OP))`: the state code, the zipper, the work
tapes and the output; an encoded action is `pair qn (pair im (pair os WA))`: the successor state
code, the input move, the output symbol and the work-tape actions. -/

/-- The encoded configuration. -/
def encE (q Zn W OP : ℕ) : ℕ := Nat.pair q (Nat.pair Zn (Nat.pair W OP))

/-- Apply an encoded action, on `pair E A`. -/
def newECode (k : ℕ) : Code :=
  .pair (pth [true, false])
    (.pair (.comp zmoveCode (.pair (pth [false, true, false]) (pth [true, true, false])))
      (.pair (.comp (wupdCode k)
          (.pair (pth [false, true, true, false]) (pth [true, true, true, true])))
        (.comp oupdCode (.pair (pth [false, true, true, true]) (pth [true, true, true, false])))))

theorem newE_spec (k : ℕ) : ∃ B, ∀ (q qn os OP : ℕ) (z : Zip) (m : SignType)
    (Ts As : Fin k → ℕ), z.md ≤ 2 → z.H ≤ 3 → os ≤ 2 →
    (∀ i, (As i).unpair.1 ≤ 3 ∧ (As i).unpair.2 ≤ 2) →
    RunsLe (newECode k)
      (Nat.pair (encE q z.enc (wenc k Ts) OP)
        (Nat.pair qn (Nat.pair (mvCode m) (Nat.pair os (wenc k As)))))
      (encE qn (z.move m).enc (wenc k (fun i => tapeUpdN (Ts i) (As i))) (oupdN OP os)) B := by
  obtain ⟨Bz, hz⟩ := zmove_spec
  obtain ⟨Bw, hw⟩ := wupd_spec k
  obtain ⟨Bo, ho⟩ := oupd_spec
  refine ⟨Bz + Bw + Bo + 100, fun q qn os OP z m Ts As hmd hH hos hA => ?_⟩
  have hX : Nat.pair (encE q z.enc (wenc k Ts) OP)
      (Nat.pair qn (Nat.pair (mvCode m) (Nat.pair os (wenc k As)))) =
      Nat.pair (Nat.pair q (Nat.pair z.enc (Nat.pair (wenc k Ts) OP)))
        (Nat.pair qn (Nat.pair (mvCode m) (Nat.pair os (wenc k As)))) := rfl
  rw [hX]
  have hz' := hz z m hmd hH
  have hw' := hw Ts As hA
  have ho' := ho OP os hos
  generalize z.enc = Zn at *
  generalize wenc k Ts = W at *
  generalize wenc k As = WA at *
  generalize mvCode m = im at *
  have p1 := pth_spec [true, false] (Nat.pair (Nat.pair q (Nat.pair Zn (Nat.pair W OP)))
    (Nat.pair qn (Nat.pair im (Nat.pair os WA))))
  have p2 := pth_spec [false, true, false] (Nat.pair (Nat.pair q (Nat.pair Zn (Nat.pair W OP)))
    (Nat.pair qn (Nat.pair im (Nat.pair os WA))))
  have p3 := pth_spec [true, true, false] (Nat.pair (Nat.pair q (Nat.pair Zn (Nat.pair W OP)))
    (Nat.pair qn (Nat.pair im (Nat.pair os WA))))
  have p4 := pth_spec [false, true, true, false] (Nat.pair (Nat.pair q (Nat.pair Zn
    (Nat.pair W OP))) (Nat.pair qn (Nat.pair im (Nat.pair os WA))))
  have p5 := pth_spec [true, true, true, true] (Nat.pair (Nat.pair q (Nat.pair Zn
    (Nat.pair W OP))) (Nat.pair qn (Nat.pair im (Nat.pair os WA))))
  have p6 := pth_spec [false, true, true, true] (Nat.pair (Nat.pair q (Nat.pair Zn
    (Nat.pair W OP))) (Nat.pair qn (Nat.pair im (Nat.pair os WA))))
  have p7 := pth_spec [true, true, true, false] (Nat.pair (Nat.pair q (Nat.pair Zn
    (Nat.pair W OP))) (Nat.pair qn (Nat.pair im (Nat.pair os WA))))
  simp only [pathVal_cons_true, pathVal_cons_false, pathVal_nil, List.length_cons,
    List.length_nil] at p1 p2 p3 p4 p5 p6 p7
  have h1 := (p2.pair p3).comp hz'
  have h2 := (p4.pair p5).comp hw'
  have h3 := (p6.pair p7).comp ho'
  exact (p1.pair (h1.pair (h2.pair h3))).mono (by omega)

end TMCode

end TimedKt
