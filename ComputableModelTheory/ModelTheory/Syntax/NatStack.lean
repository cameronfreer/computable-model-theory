/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.Encoding
import ComputableModelTheory.ModelTheory.Syntax.Primcodable

/-!
# The term stack machine on natural-number codes

`natDecodeStack` is the term stack machine (`Term.decodeStack`) transported to the level
of natural-number symbol codes: even codes are variable leaves, odd codes are function
symbols whose arity is read off the code through the language's symbol decoding. The
machine is uniform in the variable type — that uniformity is the point: it is the only
level at which the `Primcodable` instance for `Σ k, L.Term (α ⊕ Fin k)` can state its
primitive recursion witness uniformly in `k`.

This file defines the machine and its step invariants; primitive recursiveness,
soundness against each fiber's `decodeStack`, completeness on canonical codes, and
canonicalization follow in later files.
-/

open Encodable

namespace FirstOrder.Language.Term

variable (L : Language) [L.EffectiveLanguage]

/-- The arity of the function symbol coded by `c`, if any. -/
def arityOfCode (c : ℕ) : Option ℕ :=
  (decode (α := Σ i, L.Functions i) c).map (·.1)

/-- One step of the term stack machine at the level of natural-number symbol codes.
Even codes are variable leaves; odd codes are function symbols, whose arity is read off
the code. The machine is uniform in the variable type: only the language's symbol
decoding enters. -/
def natDecodeStackStep (c : ℕ) (acc : List (List ℕ)) : List (List ℕ) :=
  if c % 2 = 1 then
    match arityOfCode L (c / 2) with
    | some n => if n ≤ acc.length then (c :: (acc.take n).flatten) :: acc.drop n else []
    | none => []
  else [c] :: acc

/-- The term stack machine at the level of natural-number symbol codes. -/
def natDecodeStack (l : List ℕ) : List (List ℕ) :=
  l.foldr (natDecodeStackStep L) []

@[simp]
theorem natDecodeStack_nil : natDecodeStack L [] = [] := rfl

theorem natDecodeStack_cons (c : ℕ) (l : List ℕ) :
    natDecodeStack L (c :: l) = natDecodeStackStep L c (natDecodeStack L l) := rfl

theorem natDecodeStackStep_even {c : ℕ} (h : c % 2 = 0) (acc : List (List ℕ)) :
    natDecodeStackStep L c acc = [c] :: acc := by
  rw [natDecodeStackStep, if_neg (by omega)]

theorem natDecodeStackStep_odd_some {c n : ℕ} (h : c % 2 = 1)
    (ha : arityOfCode L (c / 2) = some n) (acc : List (List ℕ)) :
    natDecodeStackStep L c acc =
      if n ≤ acc.length then (c :: (acc.take n).flatten) :: acc.drop n else [] := by
  rw [natDecodeStackStep, if_pos h, ha]

theorem natDecodeStackStep_odd_none {c : ℕ} (h : c % 2 = 1)
    (ha : arityOfCode L (c / 2) = none) (acc : List (List ℕ)) :
    natDecodeStackStep L c acc = [] := by
  rw [natDecodeStackStep, if_pos h, ha]

/-- On the code of a variable leaf, the step pushes a singleton. -/
theorem natDecodeStackStep_encode_inl {β : Type*} [Primcodable β] (b : β)
    (acc : List (List ℕ)) :
    natDecodeStackStep L (encode (Sum.inl b : β ⊕ (Σ i, L.Functions i))) acc =
      [encode (Sum.inl b : β ⊕ (Σ i, L.Functions i))] :: acc :=
  natDecodeStackStep_even L (by rw [encode_sum_inl]; omega) acc

/-- On the code of a function symbol, the step reads off exactly that symbol's arity. -/
theorem natDecodeStackStep_encode_inr {β : Type*} [Primcodable β]
    (s : Σ i, L.Functions i) (acc : List (List ℕ)) :
    natDecodeStackStep L (encode (Sum.inr s : β ⊕ (Σ i, L.Functions i))) acc =
      if s.1 ≤ acc.length then
        (encode (Sum.inr s : β ⊕ (Σ i, L.Functions i)) :: (acc.take s.1).flatten) ::
          acc.drop s.1
      else [] := by
  have henc : encode (Sum.inr s : β ⊕ (Σ i, L.Functions i)) = 2 * encode s + 1 :=
    encode_sum_inr s
  have h1 : encode (Sum.inr s : β ⊕ (Σ i, L.Functions i)) % 2 = 1 := by omega
  have h2 : encode (Sum.inr s : β ⊕ (Σ i, L.Functions i)) / 2 = encode s := by omega
  rw [natDecodeStackStep_odd_some L h1 (by rw [h2, arityOfCode, encodek]; rfl)]

/-! ### Primitive recursiveness -/


/-- Reading the arity off a symbol code is primitive recursive. -/
theorem primrec_arityOfCode : Primrec (arityOfCode L) :=
  Primrec.option_map Primrec.decode
    (((primrec_functionSymbol_arity (L := L)).comp Primrec.snd).to₂)

/-- The code-level stack machine step is primitive recursive. -/
theorem primrec_natDecodeStackStep : Primrec₂ (natDecodeStackStep L) := by
  have hbranch : Primrec fun p : ℕ × List (List ℕ) ↦
      Option.casesOn (motive := fun _ ↦ List (List ℕ)) (arityOfCode L (p.1 / 2)) []
        fun n ↦ if n ≤ p.2.length then (p.1 :: (p.2.take n).flatten) :: p.2.drop n
          else [] := by
    have ho : Primrec fun p : ℕ × List (List ℕ) ↦ arityOfCode L (p.1 / 2) :=
      (primrec_arityOfCode L).comp
        (Primrec.nat_div.comp Primrec.fst (Primrec.const 2))
    have hg : Primrec₂ fun (p : ℕ × List (List ℕ)) (n : ℕ) ↦
        if n ≤ p.2.length then (p.1 :: (p.2.take n).flatten) :: p.2.drop n else [] := by
      have hn : Primrec fun q : (ℕ × List (List ℕ)) × ℕ ↦ q.2 := Primrec.snd
      have hacc : Primrec fun q : (ℕ × List (List ℕ)) × ℕ ↦ q.1.2 :=
        Primrec.snd.comp Primrec.fst
      exact (Primrec.ite (Primrec.nat_le.comp hn (Primrec.list_length.comp hacc))
        (Primrec.list_cons.comp
          (Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst)
            (Primrec.list_flatten.comp (Primrec.list_take.comp hn hacc)))
          (Primrec.list_drop.comp hn hacc))
        (Primrec.const [])).to₂
    exact Primrec.option_casesOn ho (Primrec.const []) hg
  have hwhole : Primrec fun p : ℕ × List (List ℕ) ↦
      if p.1 % 2 = 1 then
        Option.casesOn (motive := fun _ ↦ List (List ℕ)) (arityOfCode L (p.1 / 2)) []
          fun n ↦ if n ≤ p.2.length then (p.1 :: (p.2.take n).flatten) :: p.2.drop n
            else []
      else [p.1] :: p.2 :=
    Primrec.ite
      (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.fst (Primrec.const 2))
        (Primrec.const 1))
      hbranch
      (Primrec.list_cons.comp
        (Primrec.list_cons.comp Primrec.fst (Primrec.const [])) Primrec.snd)
  have h2 : Primrec fun p : ℕ × List (List ℕ) ↦ natDecodeStackStep L p.1 p.2 := by
    refine hwhole.of_eq fun p ↦ ?_
    rcases p with ⟨c, acc⟩
    rw [natDecodeStackStep]
    rcases arityOfCode L (c / 2) with - | n <;> rfl
  exact h2

/-- The code-level stack machine is primitive recursive. -/
theorem primrec_natDecodeStack : Primrec (natDecodeStack L) := by
  have hfold : Primrec fun l : List ℕ ↦
      l.foldr (fun c s ↦ natDecodeStackStep L c s) [] :=
    Primrec.list_foldr Primrec.id (Primrec.const [])
      (((primrec_natDecodeStackStep L).comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂)
  exact hfold.of_eq fun l ↦ rfl

end FirstOrder.Language.Term
