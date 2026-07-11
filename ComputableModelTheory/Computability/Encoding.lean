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

end Encodable
