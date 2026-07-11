/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Computability.Primrec.List

/-!
# Code-level transport lemmas

Arithmetic characterizations of mathlib's standard encodings: lists encode as lists of
element codes, sums encode by parity, and `Fin` values encode as their underlying
naturals. These are the transport lemmas for working with encoded syntax uniformly in a
type parameter — the groundwork for the uniform sigma `Primcodable` instance
`Primcodable (Σ k, L.Term (α ⊕ Fin k))` that formula codability requires: there,
uniformity in `k` can only be expressed at the level of codes.
-/

open Encodable

namespace Encodable

universe u v

variable {α : Type u} {β : Type v} [Encodable α] [Encodable β]

/-- A list encodes as the list of its element codes: the list encoding is uniform in the
element type. -/
theorem encode_list_map_encode (l : List α) : encode (l.map encode) = encode l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [Encodable.encode_list_cons, ih]

/-- The left-injection code arithmetic of the sum encoding. -/
theorem encode_sum_inl (x : α) : encode (Sum.inl x : α ⊕ β) = 2 * encode x := rfl

/-- The right-injection code arithmetic of the sum encoding. -/
theorem encode_sum_inr (y : β) : encode (Sum.inr y : α ⊕ β) = 2 * encode y + 1 := rfl

/-- `Fin` values encode as their underlying naturals. -/
theorem encode_fin_val {k : ℕ} (i : Fin k) : encode i = i.val := rfl

/-- Small naturals decode into `Fin` as themselves. -/
theorem decode_fin_of_lt {k j : ℕ} (h : j < k) : decode (α := Fin k) j = some ⟨j, h⟩ := by
  have := Encodable.encodek (⟨j, h⟩ : Fin k)
  rwa [encode_fin_val] at this

/-- Out-of-range naturals do not decode into `Fin`: the noncanonical direction needed by
canonicalization arguments. -/
theorem decode_fin_eq_none_of_le {k j : ℕ} (h : k ≤ j) : decode (α := Fin k) j = none := by
  simp [decode, Encodable.decodeSubtype, Nat.not_lt.2 h]

/-! ### Decode characterizations -/


/-- Even codes decode in a sum through the left summand. -/
theorem decode_sum_even {c : ℕ} (h : c % 2 = 0) :
    decode (α := α ⊕ β) c = (decode (α := α) (c / 2)).map Sum.inl := by
  have hb : Nat.bodd c = false := by
    rcases hb : Nat.bodd c
    · rfl
    · have := Nat.mod_two_of_bodd c
      rw [hb] at this
      simp at this
      omega
  rw [decode_sum_val]
  simp [decodeSum, hb, Nat.div2_val]

/-- Odd codes decode in a sum through the right summand. -/
theorem decode_sum_odd {c : ℕ} (h : c % 2 = 1) :
    decode (α := α ⊕ β) c = (decode (α := β) (c / 2)).map Sum.inr := by
  have hb : Nat.bodd c = true := by
    rcases hb : Nat.bodd c
    · have := Nat.mod_two_of_bodd c
      rw [hb] at this
      simp at this
      omega
    · rfl
  rw [decode_sum_val]
  simp [decodeSum, hb, Nat.div2_val]

/-- Elementwise decoding of a list of codes. -/
def decodeAll (α : Type*) [Encodable α] : List ℕ → Option (List α)
  | [] => some []
  | c :: cs => (decode (α := α) c).bind fun g ↦ (decodeAll α cs).map (g :: ·)

@[simp]
theorem decodeAll_nil : decodeAll α [] = some [] := rfl

theorem decodeAll_cons (c : ℕ) (cs : List ℕ) :
    decodeAll α (c :: cs) = (decode (α := α) c).bind fun g ↦ (decodeAll α cs).map (g :: ·) :=
  rfl

/-- Canonical codes decode elementwise to their values. -/
theorem decodeAll_map_encode (l : List α) : decodeAll α (l.map encode) = some l := by
  induction l with
  | nil => rfl
  | cons g l ih => simp [decodeAll_cons, encodek, ih]

/-- List decoding is decoding of the code list followed by elementwise decoding: the
bridge between `decode (α := List α)` and code-level computation. -/
theorem decode_list_eq_decodeAll (m : ℕ) :
    decode (α := List α) m = (decode (α := List ℕ) m).bind (decodeAll α) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => rw [decode_list_zero, decode_list_zero]; rfl
    | Nat.succ v =>
      rw [decode_list_succ, decode_list_succ, ih v.unpair.2 (Nat.lt_succ_of_le
        (Nat.unpair_right_le v))]
      rcases hd : decode (α := List ℕ) v.unpair.2 with - | cs
      · rcases h1 : decode (α := α) v.unpair.1 with - | g <;> simp [Seq.seq]
      · rcases h1 : decode (α := α) v.unpair.1 with - | g <;>
          rcases hall : decodeAll α cs with - | l <;>
            simp [Seq.seq, decodeAll_cons, h1, hall]

end Encodable
