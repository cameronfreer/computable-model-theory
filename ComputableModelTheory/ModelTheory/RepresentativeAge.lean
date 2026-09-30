/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.ModelTheory.Fraisse

/-! # Fraïssé classes from concrete representatives

Package the isomorphism closure of a family of structures using hereditary
closure on finitely generated substructures and AP/JEP on the representatives.
The index type and carrier universe are independent. No ambient limit, effective
presentation, or countability of the language is needed for the class theorem.

When the age of a structure lies in the representative class, every finite tuple factors literally
through an embedding of a representative (`exists_factor_tuple_of_age_subset`, and
`exists_factor_embedding_of_age_subset` for injective tuples). The representative and the
isomorphism are chosen classically; this is not an effective pullback of tuples.
-/

universe u v w z

namespace FirstOrder.Language

open CategoryTheory FirstOrder FirstOrder.Language

variable {L : Language.{u, v}} {I : Type z} (F : I → Bundled.{w} L.Structure)

/-- The isomorphism closure of a concrete representative family. -/
def representativeClass : Set (Bundled.{w} L.Structure) :=
  {M | ∃ i, Nonempty (M ≃[L] F i)}

theorem mem_representativeClass (i : I) : F i ∈ representativeClass F :=
  ⟨i, ⟨Language.Equiv.refl L (F i)⟩⟩

theorem representativeClass_nonempty [Nonempty I] : (representativeClass F).Nonempty :=
  ⟨F (Classical.choice inferInstance), mem_representativeClass F _⟩

theorem representativeClass_fg (hfg : ∀ i, Structure.FG L (F i))
    {M : Bundled.{w} L.Structure} (hM : M ∈ representativeClass F) : Structure.FG L M := by
  obtain ⟨i, ⟨e⟩⟩ := hM
  exact e.fg_iff.mpr (hfg i)

/-- Countability is needed for representatives only, not for the whole class. -/
theorem representativeClass_countable_quotient [Countable I] :
    (Quotient.mk' '' representativeClass F).Countable := by
  apply (Set.countable_range (fun i => Quotient.mk' (F i))).mono
  rintro _ ⟨M, ⟨i, ⟨e⟩⟩, rfl⟩
  exact ⟨i, Quotient.sound ⟨e.symm⟩⟩

/-- It suffices to recognize finitely generated substructures of representatives. -/
theorem representativeClass_hereditary
    (hsub : ∀ i (S : L.Substructure (F i)), S.FG →
      ∃ j, Nonempty (S ≃[L] F j)) : Hereditary (representativeClass F) := by
  rintro M ⟨i, ⟨e⟩⟩ N ⟨hN, ⟨f⟩⟩
  let g := e.toEmbedding.comp f
  obtain ⟨j, ⟨h⟩⟩ := hsub i g.toHom.range (hN.range g.toHom)
  exact ⟨j, ⟨h.comp g.equivRange⟩⟩

theorem representativeClass_jointEmbedding
    (hjep : ∀ i j, ∃ k, Nonempty (F i ↪[L] F k) ∧ Nonempty (F j ↪[L] F k)) :
    JointEmbedding (representativeClass F) := by
  rintro M ⟨i, ⟨e⟩⟩ N ⟨j, ⟨f⟩⟩
  obtain ⟨k, ⟨g⟩, ⟨h⟩⟩ := hjep i j
  exact ⟨F k, mem_representativeClass F k, ⟨g.comp e.toEmbedding⟩,
    ⟨h.comp f.toEmbedding⟩⟩

/-- Amalgamation of representative embeddings transfers to their isomorphism closure. -/
theorem representativeClass_amalgamation
    (hap : ∀ i j k (f : F i ↪[L] F j) (g : F i ↪[L] F k),
      ∃ (l : I) (a : F j ↪[L] F l) (b : F k ↪[L] F l), a.comp f = b.comp g) :
    Amalgamation (representativeClass F) := by
  rintro M N P f g ⟨i, ⟨eM⟩⟩ ⟨j, ⟨eN⟩⟩ ⟨k, ⟨eP⟩⟩
  obtain ⟨l, a, b, h⟩ := hap i j k
    (eN.toEmbedding.comp (f.comp eM.symm.toEmbedding))
    (eP.toEmbedding.comp (g.comp eM.symm.toEmbedding))
  refine ⟨F l, a.comp eN.toEmbedding, b.comp eP.toEmbedding,
    mem_representativeClass F l, ?_⟩
  ext x
  have hx := congrArg (fun h : F i ↪[L] F l => h (eM x)) h
  simpa only [Embedding.comp_apply, Language.Equiv.coe_toEmbedding,
    Language.Equiv.symm_apply_apply] using hx

/-- A countable family with finite generation, hereditary closure and AP/JEP
defines a Fraïssé class, without constructing any infinite structure. -/
theorem isFraisse_representativeClass [Nonempty I] [Countable I]
    (hfg : ∀ i, Structure.FG L (F i))
    (hsub : ∀ i (S : L.Substructure (F i)), S.FG → ∃ j, Nonempty (S ≃[L] F j))
    (hjep : ∀ i j, ∃ k, Nonempty (F i ↪[L] F k) ∧ Nonempty (F j ↪[L] F k))
    (hap : ∀ i j k (f : F i ↪[L] F j) (g : F i ↪[L] F k),
      ∃ (l : I) (a : F j ↪[L] F l) (b : F k ↪[L] F l), a.comp f = b.comp g) :
    IsFraisse (representativeClass F) where
  is_nonempty := representativeClass_nonempty F
  FG := fun _ h => representativeClass_fg F hfg h
  is_essentially_countable := representativeClass_countable_quotient F
  hereditary := representativeClass_hereditary F hsub
  jointEmbedding := representativeClass_jointEmbedding F hjep
  amalgamation := representativeClass_amalgamation F hap

/-! ### Finite tuples factor through representatives -/

section Factor

variable {F} {M : Type w} [L.Structure M]

/-- If the age of `M` lies in the representative class, every finite tuple of `M`, repeated
coordinates allowed, factors literally through an embedding of some representative. The
representative is isomorphic to the substructure the tuple generates, which need not be empty when
the tuple is (constants). No finite generation of the other representatives is assumed. -/
theorem exists_factor_tuple_of_age_subset (h : L.age M ⊆ representativeClass F) {n : ℕ}
    (a : Fin n → M) : ∃ (i : I) (e : F i ↪[L] M) (b : Fin n → F i), e ∘ b = a := by
  let S := Substructure.closure L (Set.range a)
  obtain ⟨i, ⟨u⟩⟩ := h (age.fg_substructure (Substructure.fg_closure (Set.finite_range a)))
  refine ⟨i, S.subtype.comp u.symm.toEmbedding,
    fun j ↦ u ⟨a j, Substructure.subset_closure (Set.mem_range_self j)⟩, ?_⟩
  funext j
  exact congrArg Subtype.val (u.symm_apply_apply _)

/-- The injective form: an injective tuple factors through an injective tuple of a
representative, with the literal equation of embeddings. -/
theorem exists_factor_embedding_of_age_subset (h : L.age M ⊆ representativeClass F) {n : ℕ}
    (a : Fin n ↪ M) :
    ∃ (i : I) (e : F i ↪[L] M) (b : Fin n ↪ F i), b.trans e.toEmbedding = a := by
  obtain ⟨i, e, b, hb⟩ := exists_factor_tuple_of_age_subset h a
  have hinj : Function.Injective (e ∘ b) := hb ▸ a.injective
  exact ⟨i, e, ⟨b, hinj.of_comp⟩, Function.Embedding.ext (congrFun hb)⟩

end Factor

end FirstOrder.Language
