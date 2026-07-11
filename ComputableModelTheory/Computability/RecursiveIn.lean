/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Computability.RecursiveIn

/-!
# Typed combinators for relative computability

This file supplements `Mathlib.Computability.RecursiveIn` with typed combinators for
`RecursiveIn` and `ComputableIn`: composition, pairing, bind, map, Boolean conditionals,
and μ-search, together with thin domain and specification wrappers for `Nat.rfind` over
total `Bool`-valued predicates. Each combinator is proved by descending to the
`Nat.RecursiveIn` constructors through `Primcodable` encodings, following the proofs of
the corresponding absolute facts in `Mathlib.Computability.Partrec`.

The typed combinators are upstream candidates for mathlib; the `Nat.rfind` wrappers are
local conveniences.
-/

open Encodable Part Primrec

section

variable {α β γ σ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]
variable {O : Set (ℕ →. ℕ)}

namespace Nat.RecursiveIn

/-- `Part.some` is recursive in any oracle set. -/
protected theorem some : Nat.RecursiveIn O Part.some :=
  Nat.Partrec.some.recursiveIn

end Nat.RecursiveIn

/-- A binary computable function is computable in any oracle set. -/
theorem Computable₂.computableIn₂ {f : α → β → σ} {O} (hf : Computable₂ f) :
    ComputableIn₂ O f :=
  hf.computableIn

namespace ComputableIn

/-- Functions extensionally equal to an oracle-computable function are oracle-computable. -/
protected theorem of_eq {f g : α → σ} (hf : ComputableIn O f) (H : ∀ a, f a = g a) :
    ComputableIn O g :=
  (funext H : f = g) ▸ hf

/-- A function is oracle-computable iff its composition with `encode` is. -/
theorem encode_iff {f : α → σ} : ComputableIn O (fun a ↦ encode (f a)) ↔ ComputableIn O f :=
  Iff.rfl

/-- `encode` is computable in any oracle set. -/
protected theorem encode : ComputableIn O (@encode α _) :=
  Computable.encode.computableIn

/-- Pairing of oracle-computable functions is oracle-computable. -/
protected theorem pair {f : α → β} {g : α → γ} (hf : ComputableIn O f)
    (hg : ComputableIn O g) : ComputableIn O fun a ↦ (f a, g a) :=
  (Nat.RecursiveIn.pair hf hg).of_eq fun n ↦ by cases decode (α := α) n <;> simp [Seq.seq]

end ComputableIn

namespace RecursiveIn

/-- Composition of an oracle-partial-recursive function with an oracle-computable function. -/
protected theorem comp {f : β →. σ} {g : α → β} (hf : RecursiveIn O f)
    (hg : ComputableIn O g) : RecursiveIn O fun a ↦ f (g a) :=
  (Nat.RecursiveIn.comp hf hg).of_eq fun n ↦ by
    simp only [map_some, bind_eq_bind]
    rcases e : decode (α := α) n with - | a <;> simp [encodek]

/-- `Part.bind` of oracle-partial-recursive functions is oracle-partial-recursive. -/
protected theorem bind {f : α →. β} {g : α → β →. σ} (hf : RecursiveIn O f)
    (hg : RecursiveIn₂ O g) : RecursiveIn O fun a ↦ (f a).bind (g a) :=
  (Nat.RecursiveIn.comp hg (Nat.RecursiveIn.pair Nat.RecursiveIn.some hf)).of_eq fun n ↦ by
    rcases e : decode (α := α) n <;> simp [Seq.seq, e, encodek]

/-- `Part.map` by an oracle-computable function preserves oracle-partial-recursiveness. -/
theorem map {f : α →. β} {g : α → β → σ} (hf : RecursiveIn O f)
    (hg : ComputableIn₂ O g) : RecursiveIn O fun a ↦ (f a).map (g a) := by
  simpa [bind_some_eq_map] using RecursiveIn.bind (g := fun a b ↦ Part.some (g a b)) hf hg

end RecursiveIn

namespace ComputableIn

/-- Composition of oracle-computable functions is oracle-computable. -/
protected theorem comp {f : β → σ} {g : α → β} (hf : ComputableIn O f)
    (hg : ComputableIn O g) : ComputableIn O fun a ↦ f (g a) :=
  RecursiveIn.comp (f := fun b ↦ Part.some (f b)) hf hg

/-- Curry an oracle-computable function on a product type. -/
theorem to₂ {f : α × β → σ} (hf : ComputableIn O f) :
    ComputableIn₂ O fun a b ↦ f (a, b) :=
  hf.of_eq fun ⟨_, _⟩ ↦ rfl

/-- An oracle-computable `Option`-valued function, viewed as a partial function, is
oracle-partial-recursive. -/
theorem ofOption {f : α → Option β} (hf : ComputableIn O f) :
    RecursiveIn O fun a ↦ (f a : Part β) :=
  (Nat.RecursiveIn.comp Nat.Partrec.ppred.recursiveIn hf).of_eq fun n ↦ by
    rcases decode (α := α) n with - | a <;> simp
    cases f a <;> simp

end ComputableIn

namespace ComputableIn₂

/-- Composition of a binary oracle-computable function with two oracle-computable functions. -/
protected theorem comp {f : β → γ → σ} {g : α → β} {h : α → γ}
    (hf : ComputableIn₂ O f) (hg : ComputableIn O g) (hh : ComputableIn O h) :
    ComputableIn O fun a ↦ f (g a) (h a) :=
  ComputableIn.comp (f := fun p : β × γ ↦ f p.1 p.2) hf (hg.pair hh)

end ComputableIn₂

namespace RecursiveIn₂

/-- Composition of a binary oracle-partial-recursive function with two oracle-computable
functions. -/
protected theorem comp {f : β → γ →. σ} {g : α → β} {h : α → γ}
    (hf : RecursiveIn₂ O f) (hg : ComputableIn O g) (hh : ComputableIn O h) :
    RecursiveIn O fun a ↦ f (g a) (h a) :=
  RecursiveIn.comp (f := fun p : β × γ ↦ f p.1 p.2) hf (hg.pair hh)

end RecursiveIn₂

namespace ComputableIn

/-- Oracle-computable functions are closed under `Bool`-valued conditionals. -/
theorem cond {c : α → Bool} {f g : α → σ} (hc : ComputableIn O c) (hf : ComputableIn O f)
    (hg : ComputableIn O g) : ComputableIn O fun a ↦ bif c a then f a else g a := by
  have harith :
      ComputableIn O fun a ↦
        encode (c a) * encode (f a) + (1 - encode (c a)) * encode (g a) :=
    Primrec.nat_add.to_comp.computableIn₂.comp
      (Primrec.nat_mul.to_comp.computableIn₂.comp (ComputableIn.encode.comp hc)
        (ComputableIn.encode.comp hf))
      (Primrec.nat_mul.to_comp.computableIn₂.comp
        (Primrec.nat_sub.to_comp.computableIn₂.comp (ComputableIn.const 1)
          (ComputableIn.encode.comp hc))
        (ComputableIn.encode.comp hg))
  exact encode_iff.1 <| harith.of_eq fun a ↦ by cases c a <;> simp

end ComputableIn

namespace RecursiveIn

/-- μ-search: unbounded minimization of an oracle-partial-recursive `Bool`-valued predicate
is oracle-partial-recursive. -/
theorem rfind {p : α → ℕ →. Bool} (hp : RecursiveIn₂ O p) :
    RecursiveIn O fun a ↦ Nat.rfind (p a) :=
  (Nat.RecursiveIn.rfind <|
        RecursiveIn.map hp
          (((Primrec.dom_bool fun b ↦ bif b then 0 else 1).comp
            Primrec.snd).to₂.to_comp.computableIn₂)).of_eq
    fun n ↦ by rcases e : decode (α := α) n <;> simp [e, Nat.rfind_zero_none, map_map, map_id']

/-- μ-search over a total `Bool`-valued predicate that is computable in `O` is
partial recursive in `O`. -/
theorem rfind_total {f : α → ℕ → Bool} (hf : ComputableIn₂ O f) :
    RecursiveIn O fun a ↦ Nat.rfind fun n ↦ Part.some (f a n) :=
  RecursiveIn.rfind (p := fun a n ↦ Part.some (f a n)) hf

end RecursiveIn

end

namespace Nat

/-- `Nat.rfind` over a total `Bool`-valued predicate halts exactly when a witness exists.
Note that `Nat.rfind` searches for the value `true`, not for `0`. This is a thin wrapper
around `Nat.rfind_dom` for the total case. -/
theorem rfind_some_dom_iff {α : Type*} {f : α → ℕ → Bool} {a : α} :
    (Nat.rfind fun n ↦ Part.some (f a n)).Dom ↔ ∃ n, f a n = true := by
  simp [Nat.rfind_dom]

/-- The result of `Nat.rfind` over a total `Bool`-valued predicate satisfies the predicate.
This is a thin wrapper around `Nat.rfind_spec` for the total case. -/
theorem rfind_some_spec {α : Type*} {f : α → ℕ → Bool} {a : α} {n : ℕ}
    (h : n ∈ Nat.rfind fun k ↦ Part.some (f a k)) : f a n = true := by
  simpa using Nat.rfind_spec h

end Nat
