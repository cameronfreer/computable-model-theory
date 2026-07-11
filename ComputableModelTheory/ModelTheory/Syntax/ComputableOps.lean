/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.ListComputable
import ComputableModelTheory.ModelTheory.Syntax.Primcodable

/-!
# Computability of term operations

Syntactic operations on terms of an effective language are primitive recursive (hence
computable). Each proof factors through the operation's *list-level shadow*: an identity
expressing `listEncode` of the operation as a list operation on `listEncode`-images
(`listEncode_relabel`, `listEncode_subst`), after which `Primrec.encode_iff` transfers
primitive recursiveness from the list level to the term level. In particular `listEncode`
itself is primitive recursive definitionally, being the term instance's `encode` read at
the list level.

Operations whose statements need `Primcodable` instances for formulas or for the uniform
sigma of terms (`func` application data, formula constructors, complexity predicates) are
deferred until those instances exist.
-/


open Encodable

namespace FirstOrder.Language.Term

universe u v u' v'

variable {L : Language.{u, v}} {α : Type u'} {β : Type v'}

/-! ### List-level shadows of term operations -/

theorem listEncode_relabel (g : α → β) (t : L.Term α) :
    (t.relabel g).listEncode = t.listEncode.map (Sum.map g id) := by
  induction t with
  | var a => rfl
  | func f ts ih =>
    rw [relabel, listEncode, listEncode, List.map_cons, List.map_flatMap]
    simp only [ih]
    rfl

theorem listEncode_subst (σf : α → L.Term β) (t : L.Term α) :
    (t.subst σf).listEncode =
      t.listEncode.flatMap
        (Sum.elim (fun a ↦ (σf a).listEncode) fun F ↦ [Sum.inr F]) := by
  induction t with
  | var a => simp [subst, listEncode]
  | func f ts ih =>
    rw [subst, listEncode, listEncode, List.flatMap_cons, List.flatMap_assoc]
    simp only [ih]
    rfl

section Primrec

variable [Primcodable α] [Primcodable β] [L.EffectiveLanguage]

/-- `listEncode` is primitive recursive: it is definitionally the `encode` of the term
instance, read back at the list level. -/
theorem primrec_listEncode :
    Primrec (listEncode : L.Term α → List (α ⊕ (Σ i, L.Functions i))) :=
  Primrec.encode_iff.1 Primrec.encode

/-- Reading the first decoded term off a symbol list is primitive recursive. -/
theorem primrec_listDecode_head? :
    Primrec fun l : List (α ⊕ (Σ i, L.Functions i)) ↦ (listDecode l).head? :=
  Primrec.encode_iff.1 <|
    (Primrec.encode.comp (Primrec.list_head?.comp primrec_decodeStack)).of_eq fun l ↦ by
      rw [decodeStack_eq_map_listEncode, List.head?_map]
      cases (listDecode l).head? <;> rfl

/-- The variable constructor is primitive recursive. -/
theorem primrec_var : Primrec (var : α → L.Term α) :=
  Primrec.encode_iff.1 <|
    (Primrec.encode.comp
      (Primrec.list_cons.comp (Primrec.sumInl : Primrec (Sum.inl : α → _))
        (Primrec.const []))).of_eq fun _ ↦ rfl

/-- Relabelling along a primitive recursive map is primitive recursive. -/
theorem primrec_relabel {g : α → β} (hg : Primrec g) :
    Primrec fun t : L.Term α ↦ t.relabel g := by
  have hsym : Primrec (Sum.map g (id : (Σ i, L.Functions i) → Σ i, L.Functions i)) :=
    Primrec.sumCasesOn Primrec.id
      ((Primrec.sumInl.comp (hg.comp Primrec.snd)).to₂)
      ((Primrec.sumInr.comp Primrec.snd).to₂) |>.of_eq fun s ↦ by cases s <;> rfl
  refine Primrec.encode_iff.1 <|
    (Primrec.encode.comp
      (Primrec.list_map primrec_listEncode ((hsym.comp Primrec.snd).to₂))).of_eq fun t ↦ ?_
  rw [show ∀ u : L.Term β, encode u = encode u.listEncode from fun _ ↦ rfl, listEncode_relabel]

/-- Substitution along a primitive recursive assignment is primitive recursive. -/
theorem primrec_subst {σf : α → L.Term β} (hσ : Primrec σf) :
    Primrec fun t : L.Term α ↦ t.subst σf := by
  have hsym : Primrec (Sum.elim (fun a ↦ (σf a).listEncode)
      (fun F : Σ i, L.Functions i ↦ ([Sum.inr F] : List (β ⊕ (Σ i, L.Functions i))))) :=
    Primrec.sumCasesOn Primrec.id
      ((primrec_listEncode.comp (hσ.comp Primrec.snd)).to₂)
      ((Primrec.list_cons.comp (Primrec.sumInr.comp Primrec.snd) (Primrec.const [])).to₂)
      |>.of_eq fun s ↦ by cases s <;> rfl
  refine Primrec.encode_iff.1 <|
    (Primrec.encode.comp
      (Primrec.list_flatMap primrec_listEncode ((hsym.comp Primrec.snd).to₂))).of_eq fun t ↦ ?_
  rw [show ∀ u : L.Term β, encode u = encode u.listEncode from fun _ ↦ rfl, listEncode_subst]

/-- The variable constructor is computable. -/
theorem computable_var : Computable (var : α → L.Term α) := primrec_var.to_comp

/-- `listEncode` is computable. -/
theorem computable_listEncode :
    Computable (listEncode : L.Term α → List (α ⊕ (Σ i, L.Functions i))) :=
  primrec_listEncode.to_comp

/-- Relabelling along a computable map is computable: the public contract. The stronger
primitive recursive form is `primrec_relabel`. -/
theorem computable_relabel {g : α → β} (hg : Computable g) :
    Computable fun t : L.Term α ↦ t.relabel g := by
  have hsym : Computable (Sum.map g (id : (Σ i, L.Functions i) → Σ i, L.Functions i)) :=
    Computable.sumCasesOn Computable.id
      ((Computable.sumInl.comp (hg.comp Computable.snd)).to₂)
      ((Computable.sumInr.comp Computable.snd).to₂) |>.of_eq fun s ↦ by cases s <;> rfl
  refine Computable.encode_iff.1 <|
    (Computable.encode.comp
      ((Computable.list_map hsym).comp computable_listEncode)).of_eq fun t ↦ ?_
  rw [show ∀ u : L.Term β, encode u = encode u.listEncode from fun _ ↦ rfl,
    listEncode_relabel]

/-- Substitution along a computable assignment is computable: the public contract. The
stronger primitive recursive form is `primrec_subst`. -/
theorem computable_subst {σf : α → L.Term β} (hσ : Computable σf) :
    Computable fun t : L.Term α ↦ t.subst σf := by
  have hsym : Computable (Sum.elim (fun a ↦ (σf a).listEncode)
      (fun F : Σ i, L.Functions i ↦ ([Sum.inr F] : List (β ⊕ (Σ i, L.Functions i))))) :=
    Computable.sumCasesOn Computable.id
      ((computable_listEncode.comp (hσ.comp Computable.snd)).to₂)
      (((Primrec.list_cons.comp Primrec.sumInr (Primrec.const [])).to_comp.comp
        Computable.snd).to₂) |>.of_eq fun s ↦ by cases s <;> rfl
  refine Computable.encode_iff.1 <|
    (Computable.encode.comp
      ((Computable.list_flatMap hsym).comp computable_listEncode)).of_eq fun t ↦ ?_
  rw [show ∀ u : L.Term β, encode u = encode u.listEncode from fun _ ↦ rfl,
    listEncode_subst]

end Primrec

end FirstOrder.Language.Term
