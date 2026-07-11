/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Syntax.EffectiveLanguage
import Mathlib.ModelTheory.Encoding

/-!
# Primitive codability of first-order syntax

Terms of an effective language over a `Primcodable` variable type are `Primcodable`,
resolving (for terms) the TODO in `Mathlib.ModelTheory.Encoding`. The instance reuses
mathlib's `Encodable (L.Term α)` verbatim; the primitive recursion witness is obtained by
shadowing `Term.listDecode` with a stack machine `decodeStack` acting on
`listEncode`-images, so that its primitive recursiveness can be stated between types that
are already `Primcodable` (`decodeStack_eq_map_listEncode` is the bridge).

Bounded formulas (packaged over all numbers of free variables), formulas, and sentences
receive `Encodable` instances on top of the term instance. Upgrading these to
`Primcodable` requires a second stack machine over the formula alphabet and a uniform
sigma `Primcodable` instance; that is future work for this file.
-/

open Encodable

namespace FirstOrder.Language

universe u v u'

variable {L : Language.{u, v}} {α : Type u'}

/-- The `Primcodable` instance of an effective language's function symbols, restated with
the sigma type spelled out so that instance search finds it under either form. -/
instance instPrimcodableSigmaFunctions [L.EffectiveLanguage] :
    Primcodable (Σ i, L.Functions i) :=
  EffectiveLanguage.instFunctionSymbols (L := L)

/-- The `Primcodable` instance of an effective language's relation symbols, restated with
the sigma type spelled out so that instance search finds it under either form. -/
instance instPrimcodableSigmaRelations [L.EffectiveLanguage] :
    Primcodable (Σ i, L.Relations i) :=
  EffectiveLanguage.instRelationSymbols (L := L)

namespace Term

/-- One step of the encoded-term stack machine: the shadow of one step of `listDecode`
acting on `listEncode`-images. -/
def decodeStackStep (g : α ⊕ (Σ i, L.Functions i))
    (acc : List (List (α ⊕ (Σ i, L.Functions i)))) :
    List (List (α ⊕ (Σ i, L.Functions i))) :=
  match g with
  | Sum.inl a => [Sum.inl a] :: acc
  | Sum.inr s =>
    if s.1 ≤ acc.length then (Sum.inr s :: (acc.take s.1).flatten) :: acc.drop s.1 else []

/-- The encoded-term stack machine: `listDecode`, viewed on `listEncode`-images. -/
def decodeStack (l : List (α ⊕ (Σ i, L.Functions i))) :
    List (List (α ⊕ (Σ i, L.Functions i))) :=
  l.foldr decodeStackStep []

private theorem take_eq_finRange_map {β : Type*} {d : List β} {n : ℕ} (h : n ≤ d.length) :
    d.take n = (List.finRange n).map fun i : Fin n ↦ d[(i : ℕ)] := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp

theorem decodeStack_eq_map_listEncode (l : List (α ⊕ (Σ i, L.Functions i))) :
    decodeStack l = (listDecode l).map listEncode := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    have hstep : decodeStack (g :: l) = decodeStackStep g (decodeStack l) := rfl
    cases g with
    | inl a =>
      rw [hstep, ih, listDecode]
      rfl
    | inr s =>
      obtain ⟨n, f⟩ := s
      rw [hstep, ih, listDecode, decodeStackStep]
      dsimp only
      rw [List.length_map]
      by_cases h : n ≤ (listDecode l).length
      · rw [dif_pos h, if_pos h, List.map_cons, listEncode, ← List.map_drop]
        congr 2
        rw [← List.map_take, ← List.flatMap_def, take_eq_finRange_map h, List.flatMap_map]
        rfl
      · rw [dif_neg h, if_neg h]
        rfl

variable [Primcodable α] [L.EffectiveLanguage]

theorem primrec_decodeStack : Primrec (decodeStack (L := L) (α := α)) := by
  have hstep : Primrec₂ (decodeStackStep (L := L) (α := α)) := by
    have hinl :
        Primrec₂ fun (p : (α ⊕ (Σ i, L.Functions i)) ×
            List (List (α ⊕ (Σ i, L.Functions i)))) (a : α) ↦
          ([Sum.inl a] : List (α ⊕ (Σ i, L.Functions i))) :: p.2 :=
      Primrec.list_cons.comp₂
        (Primrec.list_cons.comp₂ (Primrec.sumInl.comp₂ Primrec₂.right)
          (Primrec₂.const []))
        ((Primrec.snd.comp Primrec.fst).to₂)
    have hinr :
        Primrec₂ fun (p : (α ⊕ (Σ i, L.Functions i)) ×
            List (List (α ⊕ (Σ i, L.Functions i)))) (s : Σ i, L.Functions i) ↦
          if s.1 ≤ p.2.length then
            (Sum.inr s :: (p.2.take s.1).flatten) :: p.2.drop s.1
          else [] := by
      have hn : Primrec fun q : ((α ⊕ (Σ i, L.Functions i)) ×
          List (List (α ⊕ (Σ i, L.Functions i)))) × (Σ i, L.Functions i) ↦ q.2.1 :=
        (primrec_functionSymbol_arity (L := L)).comp Primrec.snd
      have hacc : Primrec fun q : ((α ⊕ (Σ i, L.Functions i)) ×
          List (List (α ⊕ (Σ i, L.Functions i)))) × (Σ i, L.Functions i) ↦ q.1.2 :=
        Primrec.snd.comp Primrec.fst
      exact (Primrec.ite (Primrec.nat_le.comp hn (Primrec.list_length.comp hacc))
        (Primrec.list_cons.comp
          (Primrec.list_cons.comp (Primrec.sumInr.comp Primrec.snd)
            (Primrec.list_flatten.comp (Primrec.list_take.comp hn hacc)))
          (Primrec.list_drop.comp hn hacc))
        (Primrec.const [])).to₂
    exact (Primrec.sumCasesOn Primrec.fst hinl hinr).of_eq fun p ↦ by
      rcases p with ⟨g | s, acc⟩ <;> rfl
  have hfold : Primrec fun l : List (α ⊕ (Σ i, L.Functions i)) ↦
      l.foldr (fun b s ↦ decodeStackStep b s) [] :=
    Primrec.list_foldr Primrec.id (Primrec.const [])
      ((hstep.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂)
  exact hfold

/-- Terms of an effective language over a `Primcodable` variable type are primitively
codable, with the same underlying `Encodable` instance as mathlib's. -/
instance instPrimcodableTerm : Primcodable (L.Term α) where
  toEncodable := inferInstance
  prim := by
    have hF : Primrec fun l : List (α ⊕ (Σ i, L.Functions i)) ↦
        (decodeStack (L := L) l).head? :=
      Primrec.list_head?.comp primrec_decodeStack
    have hG : Primrec fun n : ℕ ↦
        encode ((decode (α := List (α ⊕ (Σ i, L.Functions i))) n).bind
          fun l ↦ (decodeStack (L := L) l).head?) :=
      Primrec.encode.comp
        (Primrec.option_bind Primrec.decode ((hF.comp Primrec.snd).to₂))
    refine Primrec.nat_iff.1 (hG.of_eq fun n ↦ ?_)
    change encode ((decode (α := List (α ⊕ (Σ i, L.Functions i))) n).bind
        fun l ↦ (decodeStack (L := L) l).head?) =
      encode ((decode (α := List (α ⊕ (Σ i, L.Functions i))) n).bind
        fun l ↦ ((listDecode l).head?.bind fun a ↦ some (some a)).join)
    cases hd : decode (α := List (α ⊕ (Σ i, L.Functions i))) n with
    | none => rfl
    | some l =>
      change encode ((decodeStack (L := L) l).head?) =
        encode (((listDecode l).head?.bind fun a ↦ some (some a)).join)
      rw [decodeStack_eq_map_listEncode, List.head?_map]
      cases hh : (listDecode l).head? with
      | none => rfl
      | some t => rfl

end Term

section FormulaEncodable

variable [Primcodable α] [L.EffectiveLanguage]

/-- Bounded formulas of an effective language, packaged over all numbers of free
variables, are encodable. (`Primcodable` is future work; see the module docstring.) -/
instance instEncodableSigmaBoundedFormula : Encodable (Σ n, L.BoundedFormula α n) :=
  Encodable.ofLeftInjection (fun φ ↦ φ.2.listEncode)
    (fun l ↦ (BoundedFormula.listDecode l)[0]?) fun φ ↦ by
      have h := BoundedFormula.listDecode_encode_list [φ]
      rw [List.flatMap_singleton] at h
      rw [h]
      rfl

/-- Formulas of an effective language are encodable. -/
instance instEncodableFormula : Encodable (L.Formula α) :=
  Encodable.ofLeftInjection (fun φ ↦ (⟨0, φ⟩ : Σ n, L.BoundedFormula α n))
    (fun s ↦ match s with
      | ⟨0, φ⟩ => some φ
      | _ => none)
    fun _ ↦ rfl

end FormulaEncodable

end FirstOrder.Language
