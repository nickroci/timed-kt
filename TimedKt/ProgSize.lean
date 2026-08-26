/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import Mathlib.Computability.PartrecCode

/-!
# Program Size for `Nat.Partrec.Code`

This module defines `progSize`, the number of constructors in the syntax tree of a
`Nat.Partrec.Code`. It is ported unchanged from the parent `irreducibility` project so
that this package has no dependency on that tree.

`progSize` is a constructor count, not a bit-length. In this package it appears only in
the operational step ledger (`TimedKt.Run`), where it calibrates the write/step exchange
rate, and in the write-witness penalty of `TimedKt.WriteOnce`. The public timed
complexity `Kt` measures program length as the bit-length of an actual bitstring program
(`Kolmogorov.BitString`) and does not mention `progSize`.
-/

open Nat.Partrec

namespace TimedKt

/-- The **program size** of a code: the number of constructors in its syntax tree. -/
def progSize : Code → ℕ
  | Code.zero => 1
  | Code.succ => 1
  | Code.left => 1
  | Code.right => 1
  | Code.pair c₁ c₂ => progSize c₁ + progSize c₂ + 1
  | Code.comp c₁ c₂ => progSize c₁ + progSize c₂ + 1
  | Code.prec c₁ c₂ => progSize c₁ + progSize c₂ + 1
  | Code.rfind' c => progSize c + 1

/-- Every code has at least one constructor. -/
theorem progSize_pos (c : Code) : 0 < progSize c := by
  cases c <;> simp only [progSize] <;> omega

end TimedKt
