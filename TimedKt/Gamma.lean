/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import KolmogorovMathlib.Prefix.Encoding
import KolmogorovMathlib.Core.UniversalDecompressor
import Mathlib.Data.Nat.Size
import TimedKt.CeilLog2

/-!
# A Self-Delimiting Length Code

The triangle inequality composes two programs on one tape, so the tape must carry a
self-delimited split point. This module provides the Elias-gamma-style code used by
the composing machine (`TimedKt.Comp`): the number `n` is encoded as the unary code
of the length of its binary expansion followed by the expansion itself,

```
gammaCode n = natCode n.bits.length ++ n.bits
```

with `natCode` the unary self-delimiting code `1ᵏ0` of the `kolmogorov_complexity`
library and `n.bits` the little-endian binary expansion. The code of `n` has length
`2 * ceilLog2 (n + 1) + 1` (`gammaCode_length`) — logarithmic, which is what makes
the triangle overhead `O(log)` rather than linear.

The decoder `gammaParse` splits a leading gamma code off an arbitrary bitstring:
it reads the unary prefix, takes that many payload bits, and rejects any tape whose
payload is not in canonical form (a binary expansion never ends in a zero bit).
Canonicity makes the parse exact:

* `gammaParse_eq_some_iff` — `gammaParse r = some (n, rest)` **iff**
  `r = gammaCode n ++ rest`; in particular the parse round-trips
  (`gammaParse_gammaCode_append`) and a leading gamma code determines its number and
  the remainder uniquely (`gammaCode_append_inj`).
* `primrec_gammaParse` — the decoder is primitive recursive, which is what the
  computability proof of the composing machine consumes.

The payload value function `boolsToNat` is the little-endian binary value; the
round-trip pair is `boolsToNat_bits` and `bits_boolsToNat`.
-/

open Kolmogorov

namespace TimedKt

/-! ### The binary payload -/

/-- The little-endian binary value of a bitstring: the head is the least significant
bit. The inverse of `Nat.bits` on canonical strings. -/
def boolsToNat (l : BitString) : ℕ :=
  l.foldr (fun b n => Nat.bit b n) 0

@[simp] theorem boolsToNat_nil : boolsToNat [] = 0 := rfl

@[simp] theorem boolsToNat_cons (b : Bool) (l : BitString) :
    boolsToNat (b :: l) = Nat.bit b (boolsToNat l) := rfl

/-- `boolsToNat` inverts `Nat.bits`. -/
@[simp] theorem boolsToNat_bits (n : ℕ) : boolsToNat n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [Nat.zero_bits]
  | bit b n h ih => rw [Nat.bits_append_bit n b h, boolsToNat_cons, ih]

/-- A binary expansion is canonical: it is empty or ends in a `true` bit. Stated
through `Option.getD` so the empty case needs no side condition. -/
theorem bits_getLast?_getD (n : ℕ) : n.bits.getLast?.getD true = true := by
  induction n using Nat.binaryRec' with
  | zero => simp [Nat.zero_bits]
  | bit b n h ih =>
      rw [Nat.bits_append_bit n b h]
      cases hb : n.bits with
      | nil =>
          have hn : n = 0 := by
            have hv := boolsToNat_bits n
            rw [hb] at hv
            simpa using hv.symm
          simp [h hn]
      | cons c l =>
          rw [hb] at ih
          rw [List.getLast?_cons_cons]
          exact ih

/-- A canonical bitstring is the binary expansion of its value: `Nat.bits` inverts
`boolsToNat` on strings that are empty or end in a `true` bit. -/
theorem bits_boolsToNat : ∀ {l : BitString}, l.getLast?.getD true = true →
    (boolsToNat l).bits = l
  | [], _ => by simp [Nat.zero_bits]
  | [b], h => by
      have hb : b = true := by simpa using h
      subst hb
      have h1 : Nat.bit true 0 = 1 := by simp
      simp [h1, Nat.one_bits]
  | b :: c :: l, h => by
      have h' : (c :: l).getLast?.getD true = true := by
        rwa [List.getLast?_cons_cons] at h
      have ihm : (boolsToNat (c :: l)).bits = c :: l := bits_boolsToNat h'
      have hne : boolsToNat (c :: l) ≠ 0 := by
        intro h0
        rw [h0, Nat.zero_bits] at ihm
        exact List.cons_ne_nil c l ihm.symm
      rw [boolsToNat_cons, Nat.bits_append_bit _ _ (fun h0 => absurd h0 hne), ihm]

/-! ### The length arithmetic -/

/-- `Nat.size` is the ceiling logarithm of the successor: both are the least `k`
with `n < 2 ^ k`. -/
theorem size_eq_ceilLog2 (n : ℕ) : n.size = ceilLog2 (n + 1) := by
  refine Nat.le_antisymm ?_ ?_
  · exact Nat.size_le.mpr (Nat.lt_of_succ_le (le_two_pow_ceilLog2 (n + 1)))
  · exact ceilLog2_le_iff.mpr (Nat.succ_le_of_lt (Nat.lt_size_self n))

/-- The binary expansion of `n` has length `ceilLog2 (n + 1)`. -/
theorem bits_length_eq_ceilLog2 (n : ℕ) : n.bits.length = ceilLog2 (n + 1) := by
  rw [Nat.size_eq_bits_len, size_eq_ceilLog2]

/-! ### The code -/

/-- The **gamma code** of `n`: the unary code of the length of the binary expansion,
followed by the expansion itself. Self-delimiting, of logarithmic length. -/
def gammaCode (n : ℕ) : BitString :=
  natCode n.bits.length ++ n.bits

/-- The unary code of the library coincides with the unary prefix of its universal
decompressor, definitionally. -/
theorem natCode_eq_unaryPrefix (n : ℕ) : natCode n = unaryPrefix n := rfl

/-- The gamma code of `n` has length exactly `2 * ceilLog2 (n + 1) + 1`. -/
theorem gammaCode_length (n : ℕ) :
    (gammaCode n).length = 2 * ceilLog2 (n + 1) + 1 := by
  simp only [gammaCode, List.length_append, length_natCode, bits_length_eq_ceilLog2]
  omega

/-! ### The decoder -/

/-- The unary-prefix length read by the gamma decoder: the length of the leading
run of `true` bits. -/
def gammaPrefixLen (r : BitString) : ℕ :=
  (r.takeWhile id).length

/-- The candidate payload of the gamma decoder: the block after the unary prefix,
as long as the prefix value. -/
def gammaPayload (r : BitString) : BitString :=
  (r.drop (gammaPrefixLen r + 1)).take (gammaPrefixLen r)

/-- The remainder of the tape after the gamma code. -/
def gammaRest (r : BitString) : BitString :=
  (r.drop (gammaPrefixLen r + 1)).drop (gammaPrefixLen r)

/-- The **gamma decoder**: split a leading gamma code off a bitstring, returning the
encoded number and the remainder. Fails unless the unary prefix has a delimiter, the
payload is complete, and the payload is canonical (empty or ending in a `true` bit) —
so a successful parse recovers the tape exactly (`gammaParse_eq_some_iff`). -/
def gammaParse (r : BitString) : Option (ℕ × BitString) :=
  if gammaPrefixLen r < r.length ∧ (gammaPayload r).length = gammaPrefixLen r ∧
      (gammaPayload r).getLast?.getD true = true then
    some (boolsToNat (gammaPayload r), gammaRest r)
  else none

/-- A tape whose leading-`true` run stops strictly inside it decomposes as that run,
a `false` delimiter, and the remainder. -/
theorem takeWhile_id_decomp :
    ∀ {r : BitString}, (r.takeWhile id).length < r.length →
      r = List.replicate (r.takeWhile id).length true ++
        false :: r.drop ((r.takeWhile id).length + 1)
  | [], h => absurd h (by simp)
  | false :: r, _ => by simp
  | true :: r, h => by
      have h' : (r.takeWhile id).length < r.length := by
        simpa using h
      have ih := takeWhile_id_decomp h'
      simp only [List.takeWhile_cons_of_pos (rfl : id true = true), List.length_cons,
        List.replicate_succ, List.cons_append, List.drop_succ_cons]
      exact congrArg (List.cons true) ih

/-- **Round-trip**: the decoder splits a leading gamma code exactly. -/
@[simp] theorem gammaParse_gammaCode_append (n : ℕ) (rest : BitString) :
    gammaParse (gammaCode n ++ rest) = some (n, rest) := by
  have hassoc : gammaCode n ++ rest = unaryPrefix n.bits.length ++ (n.bits ++ rest) := by
    rw [gammaCode, natCode_eq_unaryPrefix, List.append_assoc]
  have hL : gammaPrefixLen (gammaCode n ++ rest) = n.bits.length := by
    rw [gammaPrefixLen, hassoc, takeWhile_unaryPrefix]
  have hdrop : (gammaCode n ++ rest).drop (gammaPrefixLen (gammaCode n ++ rest) + 1) =
      n.bits ++ rest := by
    rw [hL, hassoc, drop_unaryPrefix]
  have hpayload : gammaPayload (gammaCode n ++ rest) = n.bits := by
    rw [gammaPayload, hdrop, hL, List.take_left]
  have hrest : gammaRest (gammaCode n ++ rest) = rest := by
    rw [gammaRest, hdrop, hL, List.drop_left]
  have hlen : (gammaCode n ++ rest).length =
      n.bits.length + 1 + n.bits.length + rest.length := by
    simp [gammaCode, List.length_append]
    omega
  rw [gammaParse, if_pos]
  · rw [hpayload, hrest, boolsToNat_bits]
  · refine ⟨?_, ?_, ?_⟩
    · rw [hL, hlen]; omega
    · rw [hpayload, hL]
    · rw [hpayload]; exact bits_getLast?_getD n

/-- A successful parse recovers the tape: `gammaParse r = some (n, rest)` forces
`r = gammaCode n ++ rest`. -/
theorem eq_gammaCode_append_of_gammaParse {r : BitString} {n : ℕ} {rest : BitString}
    (h : gammaParse r = some (n, rest)) : r = gammaCode n ++ rest := by
  rw [gammaParse] at h
  by_cases hc : gammaPrefixLen r < r.length ∧ (gammaPayload r).length = gammaPrefixLen r ∧
      (gammaPayload r).getLast?.getD true = true
  · rw [if_pos hc] at h
    obtain ⟨hlt, hlen, hcan⟩ := hc
    obtain ⟨hn, hrest⟩ : boolsToNat (gammaPayload r) = n ∧ gammaRest r = rest := by
      have := Option.some.inj h
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    have hdecomp := takeWhile_id_decomp hlt
    have hsplit : gammaPayload r ++ gammaRest r = r.drop (gammaPrefixLen r + 1) := by
      rw [gammaPayload, gammaRest]
      exact List.take_append_drop _ _
    have hbits : (boolsToNat (gammaPayload r)).bits = gammaPayload r :=
      bits_boolsToNat hcan
    have hcode : gammaCode n = natCode (gammaPrefixLen r) ++ gammaPayload r := by
      rw [gammaCode, ← hn, hbits, hlen]
    calc r = List.replicate (gammaPrefixLen r) true ++
          false :: r.drop (gammaPrefixLen r + 1) := hdecomp
      _ = natCode (gammaPrefixLen r) ++ r.drop (gammaPrefixLen r + 1) := by
          rw [natCode]; simp
      _ = natCode (gammaPrefixLen r) ++ (gammaPayload r ++ gammaRest r) := by
          rw [hsplit]
      _ = gammaCode n ++ rest := by
          rw [← List.append_assoc, ← hcode, hrest]
  · rw [if_neg hc] at h
    exact absurd h (by simp)

/-- The decoder characterization: a parse succeeds exactly on tapes with a leading
gamma code, and recovers it. -/
theorem gammaParse_eq_some_iff {r : BitString} {n : ℕ} {rest : BitString} :
    gammaParse r = some (n, rest) ↔ r = gammaCode n ++ rest := by
  constructor
  · exact eq_gammaCode_append_of_gammaParse
  · rintro rfl
    exact gammaParse_gammaCode_append n rest

/-- Unique decodability of the gamma code as a leading block: equal tapes with
leading gamma codes agree on the number and the remainder. -/
theorem gammaCode_append_inj {m n : ℕ} {a b : BitString}
    (h : gammaCode m ++ a = gammaCode n ++ b) : m = n ∧ a = b := by
  have h1 := gammaParse_gammaCode_append m a
  rw [h, gammaParse_gammaCode_append] at h1
  have h2 := Option.some.inj h1
  exact ⟨(congrArg Prod.fst h2).symm, (congrArg Prod.snd h2).symm⟩

/-- Every gamma code is nonempty — the unary prefix always carries its delimiter. -/
theorem one_le_gammaCode_length (n : ℕ) : 1 ≤ (gammaCode n).length := by
  rw [gammaCode_length]; omega

/-! ### Computability of the decoder -/

/-- The unary-prefix length is primitive recursive, computed as the index of the
first `false` bit. -/
theorem primrec_gammaPrefixLen : Primrec gammaPrefixLen := by
  have h : Primrec fun r : BitString => r.findIdx fun b => !b :=
    Primrec.list_findIdx .id (Primrec.not.comp Primrec.snd).to₂
  exact h.of_eq fun r => (takeWhile_id_length_eq_findIdx r).symm

/-- The candidate payload is primitive recursive. -/
theorem primrec_gammaPayload : Primrec gammaPayload :=
  Primrec.list_take.comp primrec_gammaPrefixLen
    (Primrec.list_drop.comp (Primrec.succ.comp primrec_gammaPrefixLen) Primrec.id)

/-- The remainder after the payload is primitive recursive. -/
theorem primrec_gammaRest : Primrec gammaRest :=
  Primrec.list_drop.comp primrec_gammaPrefixLen
    (Primrec.list_drop.comp (Primrec.succ.comp primrec_gammaPrefixLen) Primrec.id)

/-- The little-endian binary value is primitive recursive. -/
theorem primrec_boolsToNat : Primrec boolsToNat := by
  have hbit : Primrec₂ Nat.bit := by
    have h : Primrec₂ fun (b : Bool) (n : ℕ) => bif b then 2 * n + 1 else 2 * n :=
      Primrec.cond Primrec.fst
        (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd))
        (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)
    refine h.of_eq fun b n => ?_
    cases b <;> simp
  have h : Primrec fun l : BitString =>
      l.foldr (fun b n => Nat.bit b n) 0 :=
    Primrec.list_foldr .id (Primrec.const 0)
      (hbit.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  exact h

/-- **The gamma decoder is primitive recursive.** -/
theorem primrec_gammaParse : Primrec gammaParse := by
  have hgetLast : Primrec fun r : BitString => (gammaPayload r).getLast? :=
    (Primrec.list_head?.comp (Primrec.list_reverse.comp primrec_gammaPayload)).of_eq
      fun r => List.head?_reverse
  have hc₁ : PrimrecPred fun r : BitString => gammaPrefixLen r < r.length :=
    Primrec.nat_lt.comp primrec_gammaPrefixLen Primrec.list_length
  have hc₂ : PrimrecPred fun r : BitString =>
      (gammaPayload r).length = gammaPrefixLen r :=
    Primrec.eq.comp (Primrec.list_length.comp primrec_gammaPayload) primrec_gammaPrefixLen
  have hc₃ : PrimrecPred fun r : BitString =>
      (gammaPayload r).getLast?.getD true = true :=
    Primrec.eq.comp (Primrec.option_getD.comp hgetLast (Primrec.const true))
      (Primrec.const true)
  exact Primrec.ite (hc₁.and (hc₂.and hc₃))
    (Primrec.option_some.comp
      ((primrec_boolsToNat.comp primrec_gammaPayload).pair primrec_gammaRest))
    (Primrec.const none)

end TimedKt
