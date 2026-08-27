/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import TimedKt.Comp

/-!
# The Composing Universal Machine — Computability

`compUniversal` (`TimedKt.Comp`) is defined by recursion on the tape, so its
computability does not follow from the combinators directly; this module proves it
through an iterative **stack machine** and Mathlib's `Partrec.fix`.

A machine state is a stack of pending outer programs together with the current tape
and context (`CompState`). One step (`compStep`) does one dispatch of the recursive
machine: a leaf tape runs the flagged universal machine and either returns its value
(empty stack) or pops the top program to continue on that value as context; a comp
tape parses its gamma split and pushes the outer block; every other tape is stuck.
The step function is partial recursive because its only partial ingredient is the
flagged machine itself (`compStep_eq`, `partrec_compStep`).

The fixpoint of the step function computes exactly the recursive machine
(`compUniversal_eq_fix`). The two inclusions are the **stack-adequacy** lemmas:

* `mem_fix_of_compEvalFuel` — a fueled run reaches the fixpoint, by induction on
  the fuel with the pending stack tracked through `fixResult`;
* `exists_of_mem_fix` — a fixpoint value comes from the machine, by strong
  induction on the state's total pending tape length: every step strictly
  decreases it, so the unwinding of the stack can be peeled off level by level.

The headline is `isDecompressor_compUniversal`, the field the timed machine of
`TimedKt.CompRun` consumes.
-/

open Kolmogorov

namespace TimedKt

/-- A state of the composing machine's iterative evaluator: the stack of pending
outer programs, the current tape, and the current context. -/
abbrev CompState := List BitString × BitString × BitString

/-- One step of the iterative evaluator: run a leaf through the flagged machine and
return or pop; push the outer block of a comp tape; stuck otherwise. -/
def compStep : CompState →. BitString ⊕ CompState
  | (K, false :: s, z) =>
      (flaggedUniversal (s, z)).map fun y =>
        match K with
        | [] => Sum.inl y
        | p :: K' => Sum.inr (K', p, y)
  | (K, true :: b :: r, z) =>
      match gammaParse r with
      | some (ℓ, rest) =>
          Part.some (Sum.inr (rest.take ℓ :: K, rest.drop ℓ, bif b then [] else z))
      | none => Part.none
  | _ => Part.none

theorem compStep_nil (K : List BitString) (z : BitString) :
    compStep (K, [], z) = Part.none := rfl

theorem compStep_flag_nil (K : List BitString) (z : BitString) :
    compStep (K, [true], z) = Part.none := rfl

theorem compStep_leaf_nil (s z : BitString) :
    compStep ([], false :: s, z) = (flaggedUniversal (s, z)).map Sum.inl := rfl

theorem compStep_leaf_cons (p : BitString) (K : List BitString) (s z : BitString) :
    compStep (p :: K, false :: s, z) =
      (flaggedUniversal (s, z)).map fun y => Sum.inr (K, p, y) := rfl

theorem compStep_comp_some {r : BitString} {ℓ : ℕ} {rest : BitString}
    (hp : gammaParse r = some (ℓ, rest)) (K : List BitString) (b : Bool)
    (z : BitString) :
    compStep (K, true :: b :: r, z) =
      Part.some (Sum.inr (rest.take ℓ :: K, rest.drop ℓ, bif b then [] else z)) := by
  simp only [compStep]
  rw [hp]

theorem compStep_comp_none {r : BitString} (hp : gammaParse r = none)
    (K : List BitString) (b : Bool) (z : BitString) :
    compStep (K, true :: b :: r, z) = Part.none := by
  simp only [compStep]
  rw [hp]

/-- The unwinding of a pending stack against a computed value: an empty stack
returns the value; otherwise the fixpoint continues with the top program on that
value as context. -/
def fixResult : List BitString → BitString → Part BitString
  | [], y => Part.some y
  | p :: K, y => PFun.fix compStep (K, p, y)

/-- **Stack adequacy, machine to fixpoint**: a fueled run of the recursive machine,
followed by any unwinding of the pending stack, is realized by the fixpoint of the
step function. Induction on the fuel. -/
theorem mem_fix_of_compEvalFuel :
    ∀ (k : ℕ) {s z y : BitString}, y ∈ compEvalFuel k (s, z) →
      ∀ {K : List BitString} {x : BitString}, x ∈ fixResult K y →
        x ∈ PFun.fix compStep (K, s, z) := by
  intro k
  induction k with
  | zero =>
      intro s z y hy
      rw [compEvalFuel_zero] at hy
      exact absurd hy (Part.notMem_none _)
  | succ k ih =>
      intro s z y hy K x hx
      rcases s with - | ⟨hd, tl⟩
      · rw [compEvalFuel_nil] at hy
        exact absurd hy (Part.notMem_none _)
      rcases hd
      · -- leaf tape
        rw [compEvalFuel_embed] at hy
        cases K with
        | nil =>
            obtain rfl : x = y := Part.mem_some_iff.mp hx
            refine PFun.fix_stop ?_
            rw [compStep_leaf_nil]
            exact Part.mem_map Sum.inl hy
        | cons p K' =>
            refine PFun.mem_fix_iff.mpr (Or.inr ⟨(K', p, y), ?_, ?_⟩)
            · rw [compStep_leaf_cons]
              exact Part.mem_map _ hy
            · exact hx
      · -- comp tape
        rcases tl with - | ⟨b, r⟩
        · rw [compEvalFuel_flag_nil] at hy
          exact absurd hy (Part.notMem_none _)
        cases hp : gammaParse r with
        | none =>
            rw [compEvalFuel_comp_of_parse_none hp] at hy
            exact absurd hy (Part.notMem_none _)
        | some lr =>
            obtain ⟨ℓ, rest⟩ := lr
            rw [compEvalFuel_comp_of_parse hp] at hy
            obtain ⟨m, hm, hy'⟩ := Part.mem_bind_iff.mp hy
            refine PFun.mem_fix_iff.mpr (Or.inr
              ⟨(rest.take ℓ :: K, rest.drop ℓ, bif b then [] else z), ?_, ?_⟩)
            · rw [compStep_comp_some hp]
              exact Part.mem_some _
            · exact ih hm (ih hy' hx)

/-- **Stack adequacy, fixpoint to machine**: a value of the fixpoint comes from a
run of the recursive machine on the current tape followed by the unwinding of the
stack. Strong induction on the total pending tape length, which every step
strictly decreases. -/
theorem exists_of_mem_fix :
    ∀ (n : ℕ) (K : List BitString) (s z : BitString) {x : BitString},
      s.length + (K.map List.length).sum ≤ n →
      x ∈ PFun.fix compStep (K, s, z) →
      ∃ y, y ∈ compUniversal (s, z) ∧ x ∈ fixResult K y := by
  intro n
  induction n with
  | zero =>
      intro K s z x hpot hx
      obtain rfl : s = [] := List.length_eq_zero_iff.mp (by omega)
      rcases PFun.mem_fix_iff.mp hx with h | ⟨_, h, -⟩ <;>
        rw [compStep_nil] at h <;>
        exact absurd h (Part.notMem_none _)
  | succ n ih =>
      intro K s z x hpot hx
      rcases s with - | ⟨hd, tl⟩
      · rcases PFun.mem_fix_iff.mp hx with h | ⟨_, h, -⟩ <;>
          rw [compStep_nil] at h <;>
          exact absurd h (Part.notMem_none _)
      rcases hd
      · -- leaf tape
        cases K with
        | nil =>
            rcases PFun.mem_fix_iff.mp hx with h | ⟨_, h, -⟩ <;>
              rw [compStep_leaf_nil] at h
            · obtain ⟨y, hy, heq⟩ := (Part.mem_map_iff _).mp h
              obtain rfl : y = x := Sum.inl.inj heq
              exact ⟨y, by rw [compUniversal_embed]; exact hy, Part.mem_some y⟩
            · obtain ⟨y, -, heq⟩ := (Part.mem_map_iff _).mp h
              exact absurd heq (by simp)
        | cons p K' =>
            rcases PFun.mem_fix_iff.mp hx with h | ⟨a', h, hx'⟩ <;>
              rw [compStep_leaf_cons] at h
            · obtain ⟨y, -, heq⟩ := (Part.mem_map_iff _).mp h
              exact absurd heq (by simp)
            · obtain ⟨y, hy, heq⟩ := (Part.mem_map_iff _).mp h
              obtain rfl : (K', p, y) = a' := Sum.inr.inj heq
              exact ⟨y, by rw [compUniversal_embed]; exact hy, hx'⟩
      · -- comp tape
        rcases tl with - | ⟨b, r⟩
        · rcases PFun.mem_fix_iff.mp hx with h | ⟨_, h, -⟩ <;>
            rw [compStep_flag_nil] at h <;>
            exact absurd h (Part.notMem_none _)
        cases hp : gammaParse r with
        | none =>
            rcases PFun.mem_fix_iff.mp hx with h | ⟨_, h, -⟩ <;>
              rw [compStep_comp_none hp] at h <;>
              exact absurd h (Part.notMem_none _)
        | some lr =>
            obtain ⟨ℓ, rest⟩ := lr
            have hrest : rest.length < r.length := length_rest_lt_of_gammaParse hp
            have hsplit : (rest.take ℓ).length + (rest.drop ℓ).length =
                rest.length := by
              rw [List.length_take, List.length_drop]
              omega
            simp only [List.length_cons] at hpot
            rcases PFun.mem_fix_iff.mp hx with h | ⟨a', h, hx'⟩ <;>
              rw [compStep_comp_some hp] at h
            · exact absurd (Part.mem_some_iff.mp h) (by simp)
            · obtain rfl : a' =
                  (rest.take ℓ :: K, rest.drop ℓ, bif b then [] else z) :=
                Sum.inr.inj (Part.mem_some_iff.mp h)
              obtain ⟨m, hm, hxm⟩ := ih (rest.take ℓ :: K) (rest.drop ℓ)
                (bif b then [] else z)
                (by simp only [List.map_cons, List.sum_cons]; omega) hx'
              obtain ⟨y, hy, hxy⟩ := ih K (rest.take ℓ) m (by omega) hxm
              refine ⟨y, ?_, hxy⟩
              rw [compUniversal_comp_of_parse hp]
              exact Part.mem_bind_iff.mpr ⟨m, hm, hy⟩

/-- The recursive machine is the fixpoint of the step function, started on an
empty stack. -/
theorem compUniversal_eq_fix :
    compUniversal = fun sy : BitString × BitString =>
      PFun.fix compStep ([], sy.1, sy.2) := by
  funext sy
  obtain ⟨s, z⟩ := sy
  apply Part.ext
  intro x
  constructor
  · intro hx
    exact mem_fix_of_compEvalFuel (s.length + 1) hx (Part.mem_some x)
  · intro hx
    obtain ⟨y, hy, hxy⟩ := exists_of_mem_fix s.length [] s z (by simp) hx
    obtain rfl : x = y := Part.mem_some_iff.mp hxy
    exact hy

/-! ### The step function is partial recursive -/

/-- The total dispatch of one step: the flagged machine's argument for a leaf on
the left; on the right, `some` of the pushed successor state of a comp tape, or
`none` for a stuck tape. -/
def compStepView : CompState → (BitString × BitString) ⊕ Option (BitString ⊕ CompState)
  | (_, false :: s, z) => Sum.inl (s, z)
  | (K, true :: b :: r, z) =>
      Sum.inr ((gammaParse r).map fun lr =>
        Sum.inr (lr.2.take lr.1 :: K, lr.2.drop lr.1, bif b then [] else z))
  | _ => Sum.inr none

/-- Post-processing of a leaf value against the pending stack: an empty stack
returns the value; otherwise the top program continues on it as context. -/
def stepPost (st : CompState) (y : BitString) : BitString ⊕ CompState :=
  match st.1 with
  | [] => Sum.inl y
  | p :: K' => Sum.inr (K', p, y)

/-- The step function in combinator form: dispatch through the total view, run the
flagged machine on a leaf, and strip the `Option` wrapper. This is the shape the
`Partrec` combinators consume. -/
theorem compStep_eq (st : CompState) :
    compStep st =
      (Sum.casesOn (compStepView st)
          (fun d => (flaggedUniversal d).map fun y => some (stepPost st y))
          (fun v => Part.some v) :
        Part (Option (BitString ⊕ CompState))).bind fun w => Part.ofOption w := by
  obtain ⟨K, s, z⟩ := st
  apply Part.ext
  intro w
  rcases s with - | ⟨hd, tl⟩
  · simp [compStep_nil, compStepView]
  rcases hd
  · cases K with
    | nil =>
        simp [compStep_leaf_nil, compStepView, stepPost, Part.mem_map_iff,
          Part.mem_bind_iff, eq_comm]
    | cons p K' =>
        simp [compStep_leaf_cons, compStepView, stepPost, Part.mem_map_iff,
          Part.mem_bind_iff, eq_comm]
  · rcases tl with - | ⟨b, r⟩
    · simp [compStep_flag_nil, compStepView]
    cases hp : gammaParse r with
    | none =>
        simp [compStep_comp_none hp, compStepView, hp]
    | some lr =>
        obtain ⟨ℓ, rest⟩ := lr
        simp [compStep_comp_some hp, compStepView, hp]

/-- The dispatch view is primitive recursive. -/
theorem primrec_compStepView : Primrec compStepView := by
  have htape : Primrec fun st : CompState => st.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hctx : Primrec fun st : CompState => st.2.2 :=
    Primrec.snd.comp Primrec.snd
  have htail : Primrec fun st : CompState => st.2.1.tail :=
    Primrec.list_tail.comp htape
  have htail2 : Primrec fun st : CompState => st.2.1.tail.tail :=
    Primrec.list_tail.comp htail
  have hbbit : Primrec fun st : CompState => st.2.1.tail.head?.getD false :=
    Primrec.option_getD.comp (Primrec.list_head?.comp htail) (Primrec.const false)
  have hparse : Primrec fun st : CompState => gammaParse st.2.1.tail.tail :=
    primrec_gammaParse.comp htail2
  have hpush : Primrec₂ fun (st : CompState) (lr : ℕ × BitString) =>
      (Sum.inr (lr.2.take lr.1 :: st.1, lr.2.drop lr.1,
          bif st.2.1.tail.head?.getD false then [] else st.2.2) :
        BitString ⊕ CompState) := by
    have htake : Primrec fun p : CompState × ℕ × BitString =>
        p.2.2.take p.2.1 :=
      Primrec.list_take.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)
    have hdrop : Primrec fun p : CompState × ℕ × BitString =>
        p.2.2.drop p.2.1 :=
      Primrec.list_drop.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)
    have hcons : Primrec fun p : CompState × ℕ × BitString =>
        p.2.2.take p.2.1 :: p.1.1 :=
      Primrec.list_cons.comp htake (Primrec.fst.comp Primrec.fst)
    have hcnd : Primrec fun p : CompState × ℕ × BitString =>
        bif p.1.2.1.tail.head?.getD false then ([] : BitString) else p.1.2.2 :=
      Primrec.cond (hbbit.comp Primrec.fst) (Primrec.const [])
        (hctx.comp Primrec.fst)
    exact (Primrec.sumInr.comp (hcons.pair (hdrop.pair hcnd))).to₂
  have hcompbr : Primrec fun st : CompState =>
      (Sum.inr ((gammaParse st.2.1.tail.tail).map fun lr =>
          Sum.inr (lr.2.take lr.1 :: st.1, lr.2.drop lr.1,
            bif st.2.1.tail.head?.getD false then [] else st.2.2)) :
        (BitString × BitString) ⊕ Option (BitString ⊕ CompState)) :=
    Primrec.sumInr.comp (Primrec.option_map hparse hpush)
  have hleafbr : Primrec fun st : CompState =>
      (Sum.inl (st.2.1.tail, st.2.2) :
        (BitString × BitString) ⊕ Option (BitString ⊕ CompState)) :=
    Primrec.sumInl.comp (htail.pair hctx)
  have hc₁ : PrimrecPred fun st : CompState => st.2.1.head? = some false :=
    Primrec.eq.comp (Primrec.list_head?.comp htape) (Primrec.const (some false))
  have hc₂ : PrimrecPred fun st : CompState => st.2.1.head? = some true :=
    Primrec.eq.comp (Primrec.list_head?.comp htape) (Primrec.const (some true))
  have hc₃ : PrimrecPred fun st : CompState => st.2.1.tail = [] :=
    Primrec.eq.comp htail (Primrec.const [])
  have hite : Primrec fun st : CompState =>
      if st.2.1.head? = some false then
        (Sum.inl (st.2.1.tail, st.2.2) :
          (BitString × BitString) ⊕ Option (BitString ⊕ CompState))
      else if st.2.1.head? = some true then
        if st.2.1.tail = [] then Sum.inr none
        else
          Sum.inr ((gammaParse st.2.1.tail.tail).map fun lr =>
            Sum.inr (lr.2.take lr.1 :: st.1, lr.2.drop lr.1,
              bif st.2.1.tail.head?.getD false then [] else st.2.2))
      else Sum.inr none :=
    Primrec.ite hc₁ hleafbr
      (Primrec.ite hc₂ (Primrec.ite hc₃ (Primrec.const (Sum.inr none)) hcompbr)
        (Primrec.const (Sum.inr none)))
  refine hite.of_eq fun st => ?_
  obtain ⟨K, s, z⟩ := st
  rcases s with - | ⟨hd, tl⟩
  · simp [compStepView]
  rcases hd
  · simp [compStepView]
  rcases tl with - | ⟨b, r⟩
  · simp [compStepView]
  · simp [compStepView]

/-- The stack post-processing is primitive recursive. -/
theorem primrec_stepPost : Primrec₂ stepPost := by
  have h : Primrec fun x : CompState × BitString =>
      (List.casesOn x.1.1 (Sum.inl x.2) fun p K' => Sum.inr (K', p, x.2) :
        BitString ⊕ CompState) := by
    refine Primrec.list_casesOn
      (h := fun (x : CompState × BitString) (pk : BitString × List BitString) =>
        (Sum.inr (pk.2, pk.1, x.2) : BitString ⊕ CompState))
      (Primrec.fst.comp Primrec.fst) (Primrec.sumInl.comp Primrec.snd) ?_
    exact (Primrec.sumInr.comp ((Primrec.snd.comp Primrec.snd).pair
      ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp Primrec.fst)))).to₂
  have h' : Primrec fun x : CompState × BitString => stepPost x.1 x.2 := by
    refine h.of_eq fun x => ?_
    obtain ⟨⟨K, s, z⟩, y⟩ := x
    cases K <;> rfl
  exact h'.to₂

/-- **The step function is partial recursive**: its only partial ingredient is the
flagged universal machine. -/
theorem partrec_compStep : Partrec compStep := by
  have hleft : Partrec₂ fun (st : CompState) (d : BitString × BitString) =>
      (flaggedUniversal d).map fun y => some (stepPost st y) := by
    have hflag : Partrec fun p : CompState × BitString × BitString =>
        flaggedUniversal p.2 :=
      isDecompressor_flaggedUniversal.comp Computable.snd
    have hg' : Primrec fun q : (CompState × BitString × BitString) × BitString =>
        (some (stepPost q.1.1 q.2) : Option (BitString ⊕ CompState)) :=
      Primrec.option_some.comp
        (primrec_stepPost.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
    have hg : Computable₂ fun (p : CompState × BitString × BitString)
        (y : BitString) =>
        (some (stepPost p.1 y) : Option (BitString ⊕ CompState)) :=
      hg'.to_comp.to₂
    exact (hflag.map hg).to₂
  have hright : Computable₂ fun (_ : CompState)
      (v : Option (BitString ⊕ CompState)) => v :=
    Computable.snd.to₂
  have hbig : Partrec fun st : CompState =>
      (Sum.casesOn (compStepView st)
          (fun d => (flaggedUniversal d).map fun y => some (stepPost st y))
          (fun v => Part.some v) :
        Part (Option (BitString ⊕ CompState))) :=
    Partrec.sumCasesOn_left primrec_compStepView.to_comp hleft hright
  have hbind : Partrec fun st : CompState =>
      ((Sum.casesOn (compStepView st)
          (fun d => (flaggedUniversal d).map fun y => some (stepPost st y))
          (fun v => Part.some v) :
        Part (Option (BitString ⊕ CompState))).bind fun w => Part.ofOption w) :=
    hbig.bind (Computable.ofOption Computable.snd).to₂
  exact hbind.of_eq fun st => (compStep_eq st).symm

/-- **The composing machine is a decompressor** — the computability field of the
timed machine. -/
theorem isDecompressor_compUniversal : isDecompressor compUniversal := by
  have hpair : Computable fun sy : BitString × BitString =>
      (([] : List BitString), sy.1, sy.2) :=
    (Computable.const []).pair (Computable.fst.pair Computable.snd)
  exact ((partrec_compStep.fix).comp hpair).of_eq fun sy =>
    (congrFun compUniversal_eq_fix sy).symm

end TimedKt
