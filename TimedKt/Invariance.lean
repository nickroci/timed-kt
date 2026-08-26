/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import KolmogorovMathlib.Core.Invariance
import TimedKt.UniversalRun

/-!
# Time-Side Invariance for the Timed Universal Machine

The untimed invariance theorem of the `kolmogorov_complexity` library
(`existsIsOptimalConditional`) compares decompressors by description length alone. This
module proves the timed analogue for `timedUniversal`: simulating a machine costs a
constant on the description side (the unary prefix) and a constant on the time side
(the logarithm of the linear simulation overhead).

## The comparison class

A semantic `Kolmogorov.Map` has no runtime, so the theorem quantifies over
`TimedDecompressor.Realization`: a code for the machine together with constants
`a`, `b` and a proof that every run of the machine is simulated by a `Run` of that code
in at most `a * t + b` transitions. These are exactly the overhead assumptions of the
theorem, and they are visible in its statement; nothing is inferred from the library's
`existsCodeOfIsDecompressor`, which carries no time bound.

## Main results

* `condKt_timedUniversal_le`: for every realized timed decompressor `D`,
  `Kt_U(x | y) ≤ Kt_D(x | y) + overhead`, with
  `overhead = |unary prefix of D's code| + ceilLog2 (a + b + encode code + 2)`.
* `idTimed` / `condKt_timedUniversal_le_length`: the comparison class is inhabited, and
  instantiating the theorem at the identity machine gives the standard length upper
  bound `Kt_U(x | y) ≤ |x| + O(1)`.
-/

open Nat.Partrec Kolmogorov

namespace TimedKt

namespace TimedDecompressor

/-- A **code realization** of a timed decompressor: a `Nat.Partrec.Code` simulating
every run of the machine, with output preserved and transition count linearly bounded
in the machine's own clock. The constants `a` and `b` are the simulation overhead. -/
structure Realization (D : TimedDecompressor) where
  /-- The simulating code. -/
  code : Code
  /-- Multiplicative time overhead of the simulation. -/
  a : ℕ
  /-- Additive time overhead of the simulation. -/
  b : ℕ
  /-- Every run of `D` is simulated by a `Run` of `code` on the encoded `(p, y)`,
  producing the same output within `a * t + b` transitions. -/
  sim : ∀ p y x t, D.Runs p y x t →
    ∃ T steps r, Run code (Encodable.encode (p, y)) T steps ∧
      T.getLast? = some r ∧
      x = (Encodable.decode r : Option BitString).getD [] ∧
      steps ≤ a * t + b

/-- The additive cost of running a realized machine on the universal machine: the
unary prefix on the description side, the logarithm of the linear time overhead on the
time side. -/
def Realization.overhead {D : TimedDecompressor} (R : D.Realization) : ℕ :=
  Encodable.encode R.code + 1 + ceilLog2 (R.a + R.b + Encodable.encode R.code + 2)

end TimedDecompressor

/-- **Time-side invariance.** For every timed decompressor `D` with a code realization
`R`, the timed universal machine is at most an additive constant worse:
`Kt_U(x | y) ≤ Kt_D(x | y) + R.overhead`. -/
theorem condKt_timedUniversal_le (D : TimedDecompressor) (R : D.Realization)
    (x y : BitString) :
    timedUniversal.condKt x y ≤ D.condKt x y + (R.overhead : ENat) := by
  refine sInfLeSInfAdd ?_
  rintro n ⟨p, t, hrun, rfl⟩
  have ht : 1 ≤ t := D.one_le_time p y x t hrun
  obtain ⟨T, steps, r, hsim, hlast, hx, hsteps⟩ := R.sim p y x t hrun
  have hUrun := universalRuns_of_run hsim hlast
  rw [← hx] at hUrun
  set c := Encodable.encode R.code with hc
  set t' := c + 1 + steps + 1 with ht'
  refine ⟨((programLength (unaryPrefix c ++ p) + ceilLog2 t' : ℕ) : ENat),
    ⟨unaryPrefix c ++ p, t', hUrun, rfl⟩, ?_⟩
  rw [← Nat.cast_add]
  refine Nat.cast_le.mpr ?_
  have hlen : programLength (unaryPrefix c ++ p) = c + 1 + programLength p := by
    simp [programLength, List.length_append, length_unaryPrefix]
  have ht'le : t' ≤ R.a * t + (R.b + c + 2) := by omega
  have hlog : ceilLog2 t' ≤ ceilLog2 (R.a + R.b + c + 2) + ceilLog2 t := by
    have h1 : ceilLog2 t' ≤ ceilLog2 (R.a * t + (R.b + c + 2)) := ceilLog2_mono ht'le
    have h2 := ceilLog2_linear_le R.a (R.b + c + 2) ht
    have h3 : R.a + (R.b + c + 2) = R.a + R.b + c + 2 := by omega
    rw [h3] at h2
    omega
  have hover : R.overhead = c + 1 + ceilLog2 (R.a + R.b + c + 2) := rfl
  omega

/-! ### The comparison class is inhabited

The identity machine outputs its program in one transition; `Code.left` realizes it
with constant overhead. Instantiating the invariance theorem there yields the standard
length upper bound for the timed universal machine. -/

/-- The **identity machine**: it outputs its program unchanged, in one transition. -/
def idTimed : TimedDecompressor where
  toMap := fun py => Part.some py.1
  Runs := fun p _ x t => x = p ∧ t = 1
  partrec := Computable.fst
  runs_iff_produces := by
    intro p y x
    constructor
    · intro hprod
      exact ⟨1, Part.mem_some_iff.mp hprod, rfl⟩
    · rintro ⟨t, rfl, -⟩
      exact Part.mem_some_iff.mpr rfl
  one_le_time := by
    rintro p y x t ⟨-, rfl⟩
    exact le_refl 1

/-- `idTimed.condKt x y` is exactly the length of `x` (as every program for `x` is `x`
itself, in one transition). Only the upper bound is needed below. -/
theorem idTimed_condKt_le (x y : BitString) :
    idTimed.condKt x y ≤ (programLength x : ENat) := by
  have h : idTimed.Runs x y x 1 := ⟨rfl, rfl⟩
  have := TimedDecompressor.condKt_le_of_runs h
  simpa using this

/-- `Code.left` realizes the identity machine: on the encoded `(p, y)` it projects to
`encode p` in one transition. -/
def idTimedRealization : idTimed.Realization where
  code := Code.left
  a := 0
  b := 1
  sim := by
    rintro p y x t ⟨rfl, rfl⟩
    refine ⟨[(Encodable.encode (x, y)).unpair.1], 1, Encodable.encode x,
      ?_, ?_, ?_, ?_⟩
    · exact Run.left (Encodable.encode (x, y))
    · rw [Encodable.encode_prod_val, Nat.unpair_pair]
      simp
    · rw [Encodable.encodek]
      simp
    · omega

/-- **The length upper bound.** There is a constant `c` with
`Kt_U(x | y) ≤ |x| + c` for all `x` and `y`: the timed universal machine prices any
string at its own length plus a constant. Instantiates the invariance theorem at the
identity machine, so it also witnesses that the comparison class is nonempty. -/
theorem condKt_timedUniversal_le_length :
    ∃ c : ℕ, ∀ x y : BitString,
      timedUniversal.condKt x y ≤ (programLength x : ENat) + c := by
  refine ⟨idTimedRealization.overhead, fun x y => ?_⟩
  calc timedUniversal.condKt x y
      ≤ idTimed.condKt x y + (idTimedRealization.overhead : ENat) :=
        condKt_timedUniversal_le idTimed idTimedRealization x y
    _ ≤ (programLength x : ENat) + idTimedRealization.overhead :=
        add_le_add (idTimed_condKt_le x y) le_rfl

end TimedKt
