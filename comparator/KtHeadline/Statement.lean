/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import Mathlib.Computability.PartrecCode
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Nat.Log

/-!
# Levin `Kt` on the composing universal machine: trusted statement

Definitions and claims, using Mathlib only. Read this file, not the library, to know what is
claimed. `Challenge.lean` restates the claims without proofs; `Solution.lean` proves them from the
`TimedKt` library. Layout after anthropics/formal-math `vp-vnp` (Apache-2.0).

Every definition below, except the guard machine `fastTimed` and its helpers `sqGrow`, `fastLen`,
`fastOut` (new here), is a copy of its namesake in `TimedKt` (or in the `kolmogorov_complexity`
library it builds on), with the library's abbreviations unfolded: `BitString = List Bool`,
`programLength p = p.length`, a decompressor is a `Partrec` map
`BitString × BitString →. BitString`, `produces D p y x` is `x ∈ D (p, y)`, and the unary code
`replicate n true ++ [false]`. One restructuring: the library's `TimedDecompressor.condKt` is taken
over a bare clocked relation (`condKtOf`), so `Kt_cond` needs no copy of the library's bundled
machine `timedCompUniversal` and its partial-recursiveness proof. `Solution.lean` proves the copies
agree with the library's (`Kt_cond_eq`, `KtU_cond_eq`, `condKt_eq`), so editing the library cannot
change what this file says.

## The machine, in four layers

* `Run c n T s` (Mathlib's `Nat.Partrec.Code`): code `c` on input `n` halts with write-once trace
  `T` (output last) after exactly `s` transitions, one per dispatch on a `Code` constructor. Its
  meaning is pinned to Mathlib's `Code.eval` by the claim `RunEvalSpec`.
* `UniversalRuns s y x t`: the tape `s` has unary-prefix value `i` (its leading `true`s; the next
  bit, if any, is dropped as the delimiter, so an all-ones tape has empty rest) naming the code
  `decode i`, run on `encode (rest, y)`; its output decodes to `x`; `t = (i + 1) + steps + 1`.
* `FlaggedRuns`: one context-flag bit (`true` erases the context), one transition.
* `CompRuns`, the public machine: comp flag `false` embeds a flagged run (one more transition);
  comp flag `true`, erase bit `b`, gamma code of `|p₁|`, then `p₁ ++ p₂` runs `p₂` (on `[]` or the
  context, as `b` selects) and feeds its output to `p₁`, at
  `t = t₂ + t₁ + |gammaCode |p₁|| + 2`. `CompRunsComputable` pins it to a partial recursive map.

`Kt_cond x y = min { |p| + ⌈log₂ t⌉ : CompRuns p y x t }` (an `ENat` infimum, `⊤` if no run),
`Kt x = Kt_cond x []`.

**Read before trusting the headline.** `t` counts unit-cost dispatches over unbounded naturals
(`succ`, `pair`, `unpair` cost one each); no relation to Turing-machine time is claimed. The
invariance claims (`InvarianceUniversal`, `Invariance`) quantify over a structure hypothesis
`Realization D` (a code simulating every run of `D` within `a * t + b` transitions). Guards
against vacuity: the comparison class is inhabited by the identity machine `idTimed`
(`IdTimedRealized`), whose own timed complexity is exactly the length (`IdTimedCondKt`), so the
instantiated conclusion is the finite bound `LengthBound`; `KtNil` / `FiveLeKtCond` show `Kt` is
neither `⊤` nor `0`. Separating pair for the hypothesis: the computable machine `fastTimed`
(output of length `fastLen (encode (p, y))`, clock `1`) has no realization (`FastTimedUnrealized`):
a `Run` of `s` transitions outputs at most `sqGrow^[3 s]` of its input, while `fastLen` is a
diagonal above every fixed iterate.
-/

namespace KtHeadline

open Nat.Partrec

/-- Bitstrings (`Kolmogorov.BitString`). -/
abbrev BitString := List Bool

/-- The ceiling base-two logarithm, the least `k` with `t ≤ 2 ^ k` (`TimedKt.ceilLog2`). -/
def ceilLog2 (t : ℕ) : ℕ :=
  Nat.clog 2 t

/-- **Evaluation with a transition count** (`TimedKt.Run`). `Run c n T s`: running `c` on input
`n` commits the append-only trace `T` (output last) and dispatches on exactly `s` `Code`
constructors. -/
inductive Run : Code → ℕ → List ℕ → ℕ → Prop
  | zero (n : ℕ) : Run Code.zero n [0] 1
  | succ (n : ℕ) : Run Code.succ n [Nat.succ n] 1
  | left (n : ℕ) : Run Code.left n [n.unpair.1] 1
  | right (n : ℕ) : Run Code.right n [n.unpair.2] 1
  | pair {cf cg : Code} {n : ℕ} {tf tg : List ℕ} {vf vg sf sg : ℕ} :
      Run cf n tf sf → Run cg n tg sg →
      tf.getLast? = some vf → tg.getLast? = some vg →
      Run (Code.pair cf cg) n (tf ++ tg ++ [Nat.pair vf vg]) (sf + sg + 1)
  | comp {cf cg : Code} {n : ℕ} {tg tf : List ℕ} {vg sg sf : ℕ} :
      Run cg n tg sg → tg.getLast? = some vg → Run cf vg tf sf →
      Run (Code.comp cf cg) n (tg ++ tf) (sf + sg + 1)
  | precZero {cf cg : Code} {a : ℕ} {t : List ℕ} {s : ℕ} :
      Run cf a t s → Run (Code.prec cf cg) (Nat.pair a 0) t (s + 1)
  | precSucc {cf cg : Code} {a y : ℕ} {ti tg : List ℕ} {vi si sg : ℕ} :
      Run (Code.prec cf cg) (Nat.pair a y) ti si → ti.getLast? = some vi →
      Run cg (Nat.pair a (Nat.pair y vi)) tg sg →
      Run (Code.prec cf cg) (Nat.pair a (y + 1)) (ti ++ tg) (si + sg + 1)
  | rfindFound {cf : Code} {a m : ℕ} {tx : List ℕ} {sx : ℕ} :
      Run cf (Nat.pair a m) tx sx → tx.getLast? = some 0 →
      Run (Code.rfind' cf) (Nat.pair a m) (tx ++ [m]) (sx + 1)
  | rfindStep {cf : Code} {a m x : ℕ} {tx tr : List ℕ} {sx sr : ℕ} :
      Run cf (Nat.pair a m) tx sx → tx.getLast? = some x → x ≠ 0 →
      Run (Code.rfind' cf) (Nat.pair a (m + 1)) tr sr →
      Run (Code.rfind' cf) (Nat.pair a m) (tx ++ tr) (sx + sr + 1)

/-- **The clocked universal machine** (`TimedKt.UniversalRuns`): the tape `s` has unary-prefix
value `i` (its leading run of `true`s) naming the code `decode i`, which runs on the encoded pair
of the tape after the delimiter and the context `y`; the last trace value decodes to `x`; the run
costs `t = (i + 1) + steps + 1` transitions. -/
def UniversalRuns (s y x : BitString) (t : ℕ) : Prop :=
  ∃ (code : Code) (T : List ℕ) (steps r : ℕ),
    (Encodable.decode ((s.takeWhile id).length) : Option Code) = some code ∧
    Run code (Encodable.encode (s.drop ((s.takeWhile id).length + 1), y)) T steps ∧
    T.getLast? = some r ∧
    x = (Encodable.decode r : Option BitString).getD [] ∧
    t = (s.takeWhile id).length + 1 + steps + 1

/-- **The clocked flagged machine** (`TimedKt.FlaggedRuns`): one transition for the context flag
(`true` erases the context), then a clocked universal run on the tail. -/
def FlaggedRuns (s y x : BitString) (t : ℕ) : Prop :=
  ∃ b p t', s = b :: p ∧ UniversalRuns p (bif b then [] else y) x t' ∧ t = t' + 1

/-- The unary code of `n`: `n` ones and a zero (`Kolmogorov.natCode`). -/
def unaryCode (n : ℕ) : BitString :=
  List.replicate n true ++ [false]

/-- The gamma code of `n`: the unary code of the length of the little-endian binary expansion,
then the expansion (`TimedKt.gammaCode`). -/
def gammaCode (n : ℕ) : BitString :=
  unaryCode n.bits.length ++ n.bits

/-- **The clocked composing machine** (`TimedKt.CompRuns`), the machine of the public `Kt`. -/
inductive CompRuns : BitString → BitString → BitString → ℕ → Prop
  | embed {s z x : BitString} {t : ℕ} :
      FlaggedRuns s z x t → CompRuns (false :: s) z x (t + 1)
  | comp {b : Bool} {p₁ p₂ z y x : BitString} {t₂ t₁ : ℕ} :
      CompRuns p₂ (bif b then [] else z) y t₂ →
      CompRuns p₁ y x t₁ →
      CompRuns (true :: b :: (gammaCode p₁.length ++ p₁ ++ p₂)) z x
        (t₂ + t₁ + (gammaCode p₁.length).length + 2)

/-- The candidate costs `|p| + ⌈log₂ t⌉` of producing `x` from `y` under a clocked relation
(`TimedKt.TimedDecompressor.ktCandidates`). -/
def ktCandidates (Runs : BitString → BitString → BitString → ℕ → Prop) (x y : BitString) :
    Set ENat :=
  {n | ∃ p t, Runs p y x t ∧ ((p.length + ceilLog2 t : ℕ) : ENat) = n}

/-- Conditional timed complexity of a clocked relation: the least candidate cost, `⊤` if none
(`TimedKt.TimedDecompressor.condKt`). -/
noncomputable def condKtOf (Runs : BitString → BitString → BitString → ℕ → Prop)
    (x y : BitString) : ENat :=
  sInf (ktCandidates Runs x y)

/-- **Conditional Levin complexity** `Kt(x | y)` on the composing machine (`TimedKt.Kt_cond`). -/
noncomputable def Kt_cond (x y : BitString) : ENat :=
  condKtOf CompRuns x y

/-- **Levin complexity** `Kt(x) = Kt(x | [])` (`TimedKt.Kt`). -/
noncomputable def Kt (x : BitString) : ENat :=
  Kt_cond x []

/-- Conditional timed complexity on the innermost (unflagged) universal machine
(`TimedKt.timedUniversal.condKt`). -/
noncomputable def KtU_cond (x y : BitString) : ENat :=
  condKtOf UniversalRuns x y

/-- A **timed decompressor** (`TimedKt.TimedDecompressor`): a partial recursive map with a
clocked relation, sound and complete for it, every run taking at least one transition. -/
structure TimedDecompressor where
  /-- The semantic map `(program, context) →. output`. -/
  toMap : BitString × BitString →. BitString
  /-- The clocked relation: program, context, output, transition count. -/
  Runs : BitString → BitString → BitString → ℕ → Prop
  /-- The map is partial recursive. -/
  partrec : Partrec toMap
  /-- The map produces `x` exactly when some run does. -/
  runs_iff_produces : ∀ p y x, x ∈ toMap (p, y) ↔ ∃ t, Runs p y x t
  /-- A successful run takes at least one transition. -/
  one_le_time : ∀ p y x t, Runs p y x t → 1 ≤ t

/-- `Kt_D(x | y)` (`TimedKt.TimedDecompressor.condKt`). -/
noncomputable def TimedDecompressor.condKt (D : TimedDecompressor) (x y : BitString) : ENat :=
  condKtOf D.Runs x y

/-- A **code realization** of `D` (`TimedKt.TimedDecompressor.Realization`): a code simulating
every run of `D`, same output, within `a * t + b` transitions. -/
structure Realization (D : TimedDecompressor) where
  /-- The simulating code. -/
  code : Code
  /-- Multiplicative time overhead. -/
  a : ℕ
  /-- Additive time overhead. -/
  b : ℕ
  /-- Every run of `D` is simulated by a `Run` of `code` on `encode (p, y)`. -/
  sim : ∀ p y x t, D.Runs p y x t →
    ∃ T steps r, Run code (Encodable.encode (p, y)) T steps ∧
      T.getLast? = some r ∧
      x = (Encodable.decode r : Option BitString).getD [] ∧
      steps ≤ a * t + b

/-- The invariance overhead of a realization (`TimedKt.TimedDecompressor.Realization.overhead`):
the unary prefix of the code, plus the logarithm of the linear time overhead. -/
def Realization.overhead {D : TimedDecompressor} (R : Realization D) : ℕ :=
  Encodable.encode R.code + 1 + ceilLog2 (R.a + R.b + Encodable.encode R.code + 2)

/-- Guard machine: the identity machine, which outputs its program in one transition
(`TimedKt.idTimed`). -/
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

/-- Guard growth map `v ↦ (v + 1)²`. -/
def sqGrow (v : ℕ) : ℕ :=
  (v + 1) * (v + 1)

/-- Guard output length: `sqGrow` iterated `m` times from `m`. As a diagonal it eventually exceeds
every fixed iterate of `sqGrow`. -/
def fastLen (m : ℕ) : ℕ :=
  sqGrow^[m] m

/-- Guard output: `fastLen (encode (p, y))` copies of `true`. -/
def fastOut (py : BitString × BitString) : BitString :=
  (List.cons true)^[fastLen (Encodable.encode py)] []

/-- Guard machine: outputs `fastOut (p, y)` with a clock reading one transition. A computable
machine whose clock is far too fast for any code to keep up with linearly. -/
def fastTimed : TimedDecompressor where
  toMap := fun py => Part.some (fastOut py)
  Runs := fun p y x t => x = fastOut (p, y) ∧ t = 1
  partrec := by
    have hsq : Primrec₂ fun (_ : BitString × BitString) (v : ℕ) => sqGrow v :=
      (Primrec.nat_mul.comp (Primrec.succ.comp Primrec.snd)
        (Primrec.succ.comp Primrec.snd)).to₂
    have hlen : Primrec fun py : BitString × BitString => fastLen (Encodable.encode py) :=
      Primrec.nat_iterate Primrec.encode Primrec.encode hsq
    have hcons : Primrec₂ fun (_ : BitString × BitString) (l : BitString) => true :: l :=
      (Primrec.list_cons.comp (Primrec.const true) Primrec.snd).to₂
    exact (Primrec.nat_iterate hlen (Primrec.const []) hcons).to_comp
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

/-! ## Claims -/

/-- The clock is Mathlib's semantics: `c` evaluates to `v` on `n` iff some `Run` ends in `v`. -/
def RunEvalSpec : Prop :=
  ∀ (c : Code) (n v : ℕ), v ∈ c.eval n ↔ ∃ T s, Run c n T s ∧ T.getLast? = some v

/-- Trace and transition count of a `Run` are unique. -/
def RunDeterministic : Prop :=
  ∀ (c : Code) (n : ℕ) (T₁ T₂ : List ℕ) (s₁ s₂ : ℕ),
    Run c n T₁ s₁ → Run c n T₂ s₂ → T₁ = T₂ ∧ s₁ = s₂

/-- The public machine is a partial recursive map, and `CompRuns` is its clocked semantics. -/
def CompRunsComputable : Prop :=
  ∃ M : BitString × BitString →. BitString, Partrec M ∧
    ∀ p y x, x ∈ M (p, y) ↔ ∃ t, CompRuns p y x t

/-- Output and transition count of the public machine are unique per program and context. -/
def CompRunsUnique : Prop :=
  ∀ (s z x₁ x₂ : BitString) (t₁ t₂ : ℕ),
    CompRuns s z x₁ t₁ → CompRuns s z x₂ t₂ → x₁ = x₂ ∧ t₁ = t₂

/-- **Conditioning theorem**, additive constant zero: `Kt(x | y) ≤ Kt(x)`. -/
def Conditioning : Prop :=
  ∀ x y : BitString, Kt_cond x y ≤ Kt x

/-- **Time-side invariance**, unflagged universal machine:
`Kt_U(x | y) ≤ Kt_D(x | y) + overhead` for every realized timed decompressor. -/
def InvarianceUniversal : Prop :=
  ∀ (D : TimedDecompressor) (R : Realization D) (x y : BitString),
    KtU_cond x y ≤ D.condKt x y + (R.overhead : ENat)

/-- **Invariance for the public `Kt`**: `Kt(x | y) ≤ Kt_D(x | y) + (overhead + 4)`. -/
def Invariance : Prop :=
  ∀ (D : TimedDecompressor) (R : Realization D) (x y : BitString),
    Kt_cond x y ≤ D.condKt x y + ((R.overhead + 4 : ℕ) : ENat)

/-- **Length bound**: `Kt(x | y) ≤ |x| + c` for a universal constant `c`. -/
def LengthBound : Prop :=
  ∃ c : ℕ, ∀ x y : BitString, Kt_cond x y ≤ (x.length : ENat) + c

/-- **Triangle inequality**, literal constant `7`. -/
def Triangle : Prop :=
  ∀ (x y z : BitString) (n₁ n₂ : ℕ),
    Kt_cond x y = (n₁ : ENat) → Kt_cond y z = (n₂ : ENat) →
    Kt_cond x z ≤ ((n₁ + n₂ + 3 * ceilLog2 (n₁ + 1) + 7 : ℕ) : ENat)

/-- **Easy direction of symmetry of information**, literal constant `7`. -/
def SymmetryEasy : Prop :=
  ∀ (x y : BitString) (n₁ n₂ : ℕ),
    Kt_cond x y = (n₁ : ENat) → Kt y = (n₂ : ENat) →
    Kt x ≤ ((n₁ + n₂ + 3 * ceilLog2 (n₁ + 1) + 7 : ℕ) : ENat)

/-- Universal floor: every value of `Kt_cond` is at least `5`. -/
def FiveLeKtCond : Prop :=
  ∀ x y : BitString, (5 : ENat) ≤ Kt_cond x y

/-- Exact value: `Kt [] = 5`. -/
def KtNil : Prop :=
  Kt [] = 5

/-- Guard (inhabitation witness for `Invariance`): the identity machine is realized. -/
def IdTimedRealized : Prop :=
  Nonempty (Realization idTimed)

/-- Guard: on the identity machine `Kt_D(x | y) = |x|`, so the instantiated invariance bound is
finite. -/
def IdTimedCondKt : Prop :=
  ∀ x y : BitString, idTimed.condKt x y = (x.length : ENat)

/-- Guard (separating pair, refuted side): the computable machine `fastTimed` has no realization,
so `Realization D` is a genuine restriction on `D`. -/
def FastTimedUnrealized : Prop :=
  IsEmpty (Realization fastTimed)

end KtHeadline
