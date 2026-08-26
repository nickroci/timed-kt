/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import KolmogorovMathlib.Core.UniversalDecompressor
import TimedKt.Run
import TimedKt.Timed

/-!
# The Timed Universal Machine

This module equips the `kolmogorov_complexity` library's `universalDecompressor` with a
transition count, producing the timed decompressor `timedUniversal` — the unflagged
layer beneath the public machine. The public `Kt` is defined over the flagged machine
of `TimedKt.Flagged`, which adds a one-bit context flag on top of this module.

The library's universal decompressor parses its program tape `s` as a unary prefix
(`i` ones followed by a zero) naming a `Nat.Partrec.Code`, and simulates that code on
the encoded pair of the remaining tape and the context. `UniversalRuns s y x t` replays
exactly that computation operationally, with the code execution performed by the
fuel-free evaluation relation `Run` rather than `Code.evaln`.

## Cost convention

A run on tape `s` with prefix value `i` and code execution of `steps` transitions costs

* `i + 1` transitions to scan the unary prefix,
* `steps` transitions for the code execution (`Run`'s node events), and
* `1` transition to decode the result,

so `t = (i + 1) + steps + 1`. Decoding the prefix value to a `Code` and encoding the
(remaining tape, context) pair are treated as free; every other choice is one unit per
event. These atomicity choices are fixed here and quoted in the README; the invariance
theorem is stated relative to this machine.

## Main results

* `timedUniversal_toMap`: forgetting the clock gives exactly the library's
  `universalDecompressor` — this is definitional.
* `universalRuns_iff_produces`: soundness and completeness of the clocked relation for
  the untimed semantics.
* `UniversalRuns.unique`: existence and uniqueness of the transition count for every
  successful run (from `Run.deterministic`).
* `universalRuns_of_run`: the timed simulation lemma — a `Run` of a code `c` on the
  encoded `(p, y)` yields a universal run on the tape `unaryPrefix (encode c) ++ p`.
-/

open Nat.Partrec Kolmogorov

namespace TimedKt

/-- The **clocked universal machine**. `UniversalRuns s y x t` states: parsing the tape
`s` as a unary prefix with value `i` and remainder `p`, the code named `i` runs on the
encoded pair `(p, y)` through the operational relation `Run`, its output decodes to
`x`, and the whole computation takes `t = (i + 1) + steps + 1` transitions under the
cost convention of this module. -/
def UniversalRuns (s y x : BitString) (t : ℕ) : Prop :=
  ∃ (code : Code) (T : List ℕ) (steps r : ℕ),
    (Encodable.decode ((s.takeWhile id).length) : Option Code) = some code ∧
    Run code (Encodable.encode (s.drop ((s.takeWhile id).length + 1), y)) T steps ∧
    T.getLast? = some r ∧
    x = (Encodable.decode r : Option BitString).getD [] ∧
    t = (s.takeWhile id).length + 1 + steps + 1

/-- The universal decompressor, rewritten at a decoded prefix. -/
theorem universalDecompressor_eq_of_decode {s y : BitString} {code : Code}
    (hdec : (Encodable.decode ((s.takeWhile id).length) : Option Code) = some code) :
    universalDecompressor (s, y) =
      (code.eval (Encodable.encode (s.drop ((s.takeWhile id).length + 1), y))).map
        (fun r => (Encodable.decode r : Option BitString).getD []) := by
  simp only [universalDecompressor]
  rw [hdec]

/-- A `Run` of the parsed code realizes the untimed semantics, and conversely: the
universal decompressor produces `x` from `(s, y)` exactly when some clocked run does. -/
theorem universalRuns_iff_produces (s y x : BitString) :
    produces universalDecompressor s y x ↔ ∃ t, UniversalRuns s y x t := by
  set i := (s.takeWhile id).length with hi
  set N := Encodable.encode (s.drop (i + 1), y) with hN
  obtain ⟨code, hdec⟩ : ∃ code : Code, (Encodable.decode i : Option Code) = some code :=
    ⟨Denumerable.ofNat Code i, Denumerable.decode_eq_ofNat Code i⟩
  constructor
  · intro hprod
    rw [produces, universalDecompressor_eq_of_decode hdec] at hprod
    obtain ⟨r, hr, hx⟩ := (Part.mem_map_iff _).mp hprod
    obtain ⟨k, hk⟩ := Code.evaln_complete.mp hr
    obtain ⟨T, hT, hlast⟩ := tracen_isSome_of_evaln (Option.mem_def.mp hk)
    obtain ⟨steps, hrun⟩ := exists_run_of_tracen k code hT
    exact ⟨i + 1 + steps + 1, code, T, steps, r, hdec, hrun, hlast, hx.symm, rfl⟩
  · rintro ⟨t, code', T, steps, r, hdec', hrun, hlast, hx, -⟩
    rw [hdec] at hdec'
    obtain rfl : code = code' := Option.some.inj hdec'
    obtain ⟨k, hk⟩ := exists_tracen_of_run hrun
    have hev : Code.evaln k code N = some r := by
      rw [evaln_of_tracen hk, hlast]
    have hr : r ∈ code.eval N := Code.evaln_sound (Option.mem_def.mpr hev)
    rw [produces, universalDecompressor_eq_of_decode hdec]
    exact (Part.mem_map_iff _).mpr ⟨r, hr, hx.symm⟩

/-- **Existence and uniqueness of the transition count.** Two clocked runs on the same
tape and context agree on output and on the count. -/
theorem UniversalRuns.unique {s y x₁ x₂ : BitString} {t₁ t₂ : ℕ}
    (h₁ : UniversalRuns s y x₁ t₁) (h₂ : UniversalRuns s y x₂ t₂) :
    x₁ = x₂ ∧ t₁ = t₂ := by
  obtain ⟨c₁, T₁, s₁, r₁, hdec₁, hrun₁, hlast₁, hx₁, ht₁⟩ := h₁
  obtain ⟨c₂, T₂, s₂, r₂, hdec₂, hrun₂, hlast₂, hx₂, ht₂⟩ := h₂
  rw [hdec₁] at hdec₂
  obtain rfl : c₁ = c₂ := Option.some.inj hdec₂
  obtain ⟨rfl, rfl⟩ := hrun₁.deterministic hrun₂
  rw [hlast₁] at hlast₂
  obtain rfl : r₁ = r₂ := Option.some.inj hlast₂
  exact ⟨hx₁.trans hx₂.symm, ht₁.trans ht₂.symm⟩

/-- **Timed simulation.** A `Run` of a code `c` on the encoded pair `(p, y)` yields a
clocked universal run on the tape `unaryPrefix (encode c) ++ p`, at cost
`(encode c + 1) + steps + 1`. -/
theorem universalRuns_of_run {c : Code} {p y : BitString} {T : List ℕ} {steps r : ℕ}
    (hrun : Run c (Encodable.encode (p, y)) T steps) (hlast : T.getLast? = some r) :
    UniversalRuns (unaryPrefix (Encodable.encode c) ++ p) y
      ((Encodable.decode r : Option BitString).getD [])
      (Encodable.encode c + 1 + steps + 1) := by
  refine ⟨c, T, steps, r, ?_, ?_, hlast, rfl, ?_⟩
  · rw [takeWhile_unaryPrefix, Encodable.encodek]
  · rw [takeWhile_unaryPrefix, drop_unaryPrefix]
    exact hrun
  · rw [takeWhile_unaryPrefix]

/-- The **timed universal machine**: the library's `universalDecompressor` together
with the clocked relation `UniversalRuns`. -/
def timedUniversal : TimedDecompressor where
  toMap := universalDecompressor
  Runs := UniversalRuns
  partrec := isDecompressorUniversalDecompressor
  runs_iff_produces := universalRuns_iff_produces
  one_le_time := by
    rintro p y x t ⟨-, -, -, -, -, -, -, -, rfl⟩
    omega

/-- Forgetting the clock gives exactly the library's universal decompressor. -/
theorem timedUniversal_toMap : timedUniversal.toMap = universalDecompressor := rfl

end TimedKt
