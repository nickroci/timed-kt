/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import KolmogorovMathlib.Core.Basic
import TimedKt.CeilLog2

/-!
# Timed Decompressors and the Timed Complexity `Kt`

A `TimedDecompressor` is a decompressor in the sense of the `kolmogorov_complexity`
library — a partial recursive map `(program, context) →. output` over bitstrings —
together with an operational relation `Runs p y x t` recording that the machine maps
`(p, y)` to `x` in exactly `t` transitions. The two layers are tied by
`runs_iff_produces`: the map produces `x` exactly when some run does. Output
determinism is inherited from the semantic layer (`Runs.output_unique`); a successful
run takes at least one transition (`one_le_time`).

On this interface the timed complexity is

* `condKt D x y = min { |p| + ceilLog2 t : Runs p y x t }`, as an `ENat` infimum in the
  shape of the library's `condK`, and
* `plainKt D x = condKt D x []`.

Program length is bitstring length (`Kolmogorov.programLength`) and `t` counts
transitions of the operational relation; no other quantity enters the definition.

## Main results

* `condK_le_condKt`: dropping the clock can only shrink the cost, so the library's
  untimed `condK` is a lower bound for `condKt` over the same machine.
* `condKt_le_of_runs`: the witness upper bound from any concrete run.
* `condKt_lt_top_iff`: `condKt` is finite exactly on producible outputs.
-/

namespace TimedKt

open Kolmogorov

/-- A **timed decompressor**: a decompressor together with an operational relation
recording exact transition counts. `Runs p y x t` reads: on program `p` and context
`y`, the machine halts with output `x` after exactly `t` transitions. -/
structure TimedDecompressor where
  /-- The underlying semantic map `(program, context) →. output`. -/
  toMap : Map
  /-- The operational relation: program, context, output, transition count. -/
  Runs : BitString → BitString → BitString → ℕ → Prop
  /-- The semantic map is partial recursive. -/
  partrec : isDecompressor toMap
  /-- Soundness and completeness: the map produces `x` exactly when some run does. -/
  runs_iff_produces : ∀ p y x, produces toMap p y x ↔ ∃ t, Runs p y x t
  /-- A successful run takes at least one transition. -/
  one_le_time : ∀ p y x t, Runs p y x t → 1 ≤ t

namespace TimedDecompressor

variable (D : TimedDecompressor)

/-- Output determinism: two runs on the same program and context produce the same
output. Inherited from single-valuedness of the semantic layer. -/
theorem Runs.output_unique {D : TimedDecompressor} {p y x₁ x₂ : BitString} {t₁ t₂ : ℕ}
    (h₁ : D.Runs p y x₁ t₁) (h₂ : D.Runs p y x₂ t₂) : x₁ = x₂ :=
  Part.mem_unique ((D.runs_iff_produces p y x₁).mpr ⟨t₁, h₁⟩)
    ((D.runs_iff_produces p y x₂).mpr ⟨t₂, h₂⟩)

/-- The candidate timed costs of producing `x` from `y`: all values
`|p| + ceilLog2 t` over runs `Runs p y x t`. -/
def ktCandidates (x y : BitString) : Set ENat :=
  {n | ∃ p t, D.Runs p y x t ∧ ((programLength p + ceilLog2 t : ℕ) : ENat) = n}

/-- **Conditional timed complexity** `Kt_D(x | y)`: the least `|p| + ceilLog2 t` over
all programs `p` and transition counts `t` with `Runs p y x t`, or `⊤` when no run
produces `x`. -/
noncomputable def condKt (x y : BitString) : ENat :=
  sInf (D.ktCandidates x y)

/-- **Plain timed complexity** `Kt_D(x)`: the conditional complexity with an empty
context. -/
noncomputable def plainKt (x : BitString) : ENat :=
  D.condKt x []

/-- The witness upper bound: any concrete run prices the output. -/
theorem condKt_le_of_runs {D : TimedDecompressor} {p y x : BitString} {t : ℕ}
    (h : D.Runs p y x t) :
    D.condKt x y ≤ ((programLength p + ceilLog2 t : ℕ) : ENat) :=
  sInf_le ⟨p, t, h, rfl⟩

/-- Dropping the clock can only shrink the cost: the untimed conditional complexity of
the underlying decompressor bounds `condKt` from below. -/
theorem condK_le_condKt (x y : BitString) : condK D.toMap x y ≤ D.condKt x y := by
  refine le_sInf ?_
  rintro n ⟨p, t, hrun, rfl⟩
  have hprod : produces D.toMap p y x := (D.runs_iff_produces p y x).mpr ⟨t, hrun⟩
  calc condK D.toMap x y ≤ ((programLength p : ℕ) : ENat) := sInf_le ⟨p, hprod, rfl⟩
    _ ≤ ((programLength p + ceilLog2 t : ℕ) : ENat) := by
        exact_mod_cast Nat.le_add_right _ _

/-- The untimed plain complexity bounds `plainKt` from below. -/
theorem plainK_le_plainKt (x : BitString) : plainK D.toMap x ≤ D.plainKt x :=
  D.condK_le_condKt x []

/-- `condKt` is finite exactly when some run — equivalently, the underlying
decompressor — produces `x` from `y`. -/
theorem condKt_lt_top_iff {D : TimedDecompressor} {x y : BitString} :
    D.condKt x y < ⊤ ↔ ∃ p, produces D.toMap p y x := by
  constructor
  · intro h
    obtain ⟨n, hn, -⟩ := sInf_lt_iff.mp h
    obtain ⟨p, t, hrun, rfl⟩ := hn
    exact ⟨p, (D.runs_iff_produces p y x).mpr ⟨t, hrun⟩⟩
  · rintro ⟨p, hprod⟩
    obtain ⟨t, hrun⟩ := (D.runs_iff_produces p y x).mp hprod
    exact lt_of_le_of_lt (condKt_le_of_runs hrun) (ENat.natCast_lt_top _)

end TimedDecompressor

end TimedKt
