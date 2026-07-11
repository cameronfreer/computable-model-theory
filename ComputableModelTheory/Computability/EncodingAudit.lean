/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.Encoding
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for code-level transport lemmas

Named acceptance tests for the encoding groundwork, including the invalid/noncanonical
decoding behavior that canonicalization arguments rely on. Checked by
`#assert_standard_axioms`; outside the root import spine; CI checks it explicitly with

```
lake env lean ComputableModelTheory/Computability/EncodingAudit.lean
```
-/

open Encodable

section

variable {α β : Type*} [Encodable α] [Encodable β]

/-- List transport: a list encodes as the list of its element codes. -/
theorem test_encode_list_map_encode (l : List α) : encode (l.map encode) = encode l :=
  encode_list_map_encode l

/-- Sum transport: left injections take even codes. -/
theorem test_encode_sum_inl (x : α) : encode (Sum.inl x : α ⊕ β) = 2 * encode x :=
  encode_sum_inl x

/-- Sum transport: right injections take odd codes. -/
theorem test_encode_sum_inr (y : β) : encode (Sum.inr y : α ⊕ β) = 2 * encode y + 1 :=
  encode_sum_inr y

/-- Fin transport: values encode as their underlying naturals. -/
theorem test_encode_fin_val {k : ℕ} (i : Fin k) : encode i = i.val :=
  encode_fin_val i

/-- Valid codes decode into `Fin` canonically. -/
theorem test_decode_fin_of_lt {k j : ℕ} (h : j < k) :
    decode (α := Fin k) j = some ⟨j, h⟩ :=
  decode_fin_of_lt h

/-- Invalid codes do not decode into `Fin`. -/
theorem test_decode_fin_eq_none_of_le {k j : ℕ} (h : k ≤ j) :
    decode (α := Fin k) j = none :=
  decode_fin_eq_none_of_le h

/-- The two `Fin` directions together characterize decoding completely. -/
theorem test_decode_fin_iff {k j : ℕ} :
    (decode (α := Fin k) j).isSome ↔ j < k := by
  rcases Nat.lt_or_ge j k with h | h
  · simp [decode_fin_of_lt h, h]
  · simp [decode_fin_eq_none_of_le h, Nat.not_lt.2 h]

/-- Even codes decode in sums through the left summand. -/
theorem test_decode_sum_even {c : ℕ} (h : c % 2 = 0) :
    decode (α := α ⊕ β) c = (decode (α := α) (c / 2)).map Sum.inl :=
  decode_sum_even h

/-- Odd codes decode in sums through the right summand. -/
theorem test_decode_sum_odd {c : ℕ} (h : c % 2 = 1) :
    decode (α := α ⊕ β) c = (decode (α := β) (c / 2)).map Sum.inr :=
  decode_sum_odd h

/-- List decoding factors through the code list and elementwise decoding. -/
theorem test_decode_list_eq_decodeAll (m : ℕ) :
    decode (α := List α) m = (decode (α := List ℕ) m).bind (decodeAll α) :=
  decode_list_eq_decodeAll m

/-- Canonical code lists decode elementwise to their values. -/
theorem test_decodeAll_map_encode (l : List α) : decodeAll α (l.map encode) = some l :=
  decodeAll_map_encode l

end

#assert_standard_axioms test_encode_list_map_encode
#assert_standard_axioms test_decode_sum_even
#assert_standard_axioms test_decode_sum_odd
#assert_standard_axioms test_decode_list_eq_decodeAll
#assert_standard_axioms test_decodeAll_map_encode
#assert_standard_axioms test_encode_sum_inl
#assert_standard_axioms test_encode_sum_inr
#assert_standard_axioms test_encode_fin_val
#assert_standard_axioms test_decode_fin_of_lt
#assert_standard_axioms test_decode_fin_eq_none_of_le
#assert_standard_axioms test_decode_fin_iff
