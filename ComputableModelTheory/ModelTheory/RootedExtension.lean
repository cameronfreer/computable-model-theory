/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.RepresentativeAge

/-! # Rooted universality and uniqueness

Thin adapters over Mathlib's back-and-forth engines `embedding_from_cg` and `equiv_between_cg`. No
new back-and-forth construction is made here.

* **Rooted interfaces.** For a finitely generated root `A` with `aM : A ↪[L] M` and
  `aN : A ↪[L] N`, an extension pair gives `e : M ↪[L] N` with `e.comp aM = aN`
  (`exists_embedding_comp_eq_of_isExtensionPair`, countable generation of `M` only), and extension
  pairs both ways give `e : M ≃[L] N` with `e.toEmbedding.comp aM = aN`
  (`exists_equiv_comp_eq_of_isExtensionPair`, countable generation of both).
* **The seed is supplied, not assumed away.** An extension pair can hold vacuously when no partial
  isomorphism exists at all — a constant or a nullary relation can obstruct the first map — so
  every theorem here takes the root explicitly.
* **The family adapter.** `ExtendsRepresentatives F N` says that `N` extends every embedding of a
  representative into `N` along every embedding of that representative into another. If the age of
  `M` lies in `representativeClass F`, this yields `L.IsExtensionPair M N`
  (`isExtensionPair_of_age_subset`). Age containment supplies representatives for both finitely
  generated substructures of an extension step, so no hereditary closure is assumed.
* **Universality and uniqueness** for a family of finitely generated structures:
  `exists_embedding_comp_eq_of_age_subset` assumes nothing of the target's age or countability (its
  age may be strictly larger); `exists_equiv_comp_eq_of_age_subset` assumes the hypotheses on both
  sides. Countable-carrier forms follow from `Structure.cg_of_countable`.

All choices are classical; nothing here is effective.
-/

universe u v w w' z x

namespace FirstOrder.Language

open CategoryTheory FirstOrder Structure Substructure

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]
  {A : Type x} [L.Structure A]

/-! ### Rooted embeddings and equivalences from extension pairs -/

/-- The partial isomorphism `aM(A) ≅ aN(A)` determined by a root. -/
private noncomputable def rootPartialEquiv (aM : A ↪[L] M) (aN : A ↪[L] N) : M ≃ₚ[L] N :=
  ⟨aM.toHom.range, aN.toHom.range, aN.equivRange.comp aM.equivRange.symm⟩

private theorem rootPartialEquiv_dom_fg (hA : Structure.FG L A) (aM : A ↪[L] M)
    (aN : A ↪[L] N) : (rootPartialEquiv aM aN).dom.FG :=
  hA.range aM.toHom

/-- An embedding extending the root's partial isomorphism satisfies the root equation. -/
private theorem comp_eq_of_le {aM : A ↪[L] M} {aN : A ↪[L] N} {f : M ↪[L] N}
    (h : rootPartialEquiv aM aN ≤ f.toPartialEquiv) : f.comp aM = aN := by
  ext a
  obtain ⟨_, heq⟩ := h
  have ha : f (aM a) = aN.equivRange (aM.equivRange.symm ⟨aM a, ⟨a, rfl⟩⟩) :=
    DFunLike.congr_fun heq ⟨aM a, ⟨a, rfl⟩⟩
  have hsymm : aM.equivRange.symm ⟨aM a, ⟨a, rfl⟩⟩ = a :=
    aM.equivRange.symm_apply_eq.2 (Subtype.ext (Embedding.equivRange_apply aM a).symm)
  rw [hsymm, Embedding.equivRange_apply] at ha
  exact ha

/-- **Rooted universality from an extension pair.** A finitely generated root embedded in both
structures extends to an embedding of the countably generated `M` into `N` that commutes with the
root. No countability or age hypothesis on `N`. -/
theorem exists_embedding_comp_eq_of_isExtensionPair (hA : Structure.FG L A) (aM : A ↪[L] M)
    (aN : A ↪[L] N) (hM : Structure.CG L M) (H : L.IsExtensionPair M N) :
    ∃ e : M ↪[L] N, e.comp aM = aN := by
  obtain ⟨e, he⟩ := embedding_from_cg hM ⟨rootPartialEquiv aM aN,
    rootPartialEquiv_dom_fg hA aM aN⟩ H
  exact ⟨e, comp_eq_of_le he⟩

/-- **Rooted uniqueness from extension pairs both ways.** Two countably generated structures with
extension pairs in both directions are isomorphic over any finitely generated common root. -/
theorem exists_equiv_comp_eq_of_isExtensionPair (hA : Structure.FG L A) (aM : A ↪[L] M)
    (aN : A ↪[L] N) (hM : Structure.CG L M) (hN : Structure.CG L N) (H : L.IsExtensionPair M N)
    (H' : L.IsExtensionPair N M) : ∃ e : M ≃[L] N, e.toEmbedding.comp aM = aN := by
  obtain ⟨e, he⟩ := equiv_between_cg hM hN ⟨rootPartialEquiv aM aN,
    rootPartialEquiv_dom_fg hA aM aN⟩ H H'
  exact ⟨e, comp_eq_of_le he⟩

/-! ### The family adapter -/

section Family

variable {I : Type z} {F : I → Bundled.{w} L.Structure}

/-- `N` extends the representatives' embeddings: every embedding of a representative into `N`
extends along every embedding of that representative into another representative. This concerns
maps between whole representatives; `isExtensionPair_of_age_subset` transports it to the finitely
generated substructures of a structure whose age lies in the representative class. -/
def ExtendsRepresentatives (F : I → Bundled.{w} L.Structure) (N : Type w') [L.Structure N] :
    Prop :=
  ∀ i j (f : F i ↪[L] F j) (g : F i ↪[L] N), ∃ h : F j ↪[L] N, h.comp f = g

/-- **The family adapter.** If the age of `M` lies in the representative class and `N` extends the
representatives' embeddings, then `(M, N)` is an extension pair. The two finitely generated
substructures of each extension step are both in the age, so each has a representative; no
hereditary closure, countability or age hypothesis on `N` is used. -/
theorem isExtensionPair_of_age_subset (hM : L.age M ⊆ representativeClass F)
    (hN : ExtendsRepresentatives F N) : L.IsExtensionPair M N := by
  rw [isExtensionPair_iff_exists_embedding_closure_singleton_sup]
  intro S hS f m
  let T : L.Substructure M := closure L {m} ⊔ S
  have hST : S ≤ T := le_sup_right
  obtain ⟨i, ⟨u⟩⟩ := hM (age.fg_substructure hS)
  obtain ⟨j, ⟨v⟩⟩ := hM (age.fg_substructure ((fg_closure_singleton m).sup hS))
  obtain ⟨h, hh⟩ := hN i j (v.toEmbedding.comp ((Substructure.inclusion hST).comp
    u.symm.toEmbedding)) (f.comp u.symm.toEmbedding)
  refine ⟨h.comp v.toEmbedding, ?_⟩
  ext s
  have hs : h (v (Substructure.inclusion hST (u.symm (u s)))) = f (u.symm (u s)) :=
    DFunLike.congr_fun hh (u s)
  rw [Language.Equiv.symm_apply_apply] at hs
  exact hs.symm

/-- **Relative universality over a root.** If the age of the countably generated `M` lies in the
representative class and `N` extends the representatives' embeddings, every finitely generated
common root extends to an embedding `M ↪[L] N`. Nothing is assumed of `N`'s age, which may be
strictly larger, or of its cardinality. -/
theorem exists_embedding_comp_eq_of_age_subset (hM : L.age M ⊆ representativeClass F)
    (hN : ExtendsRepresentatives F N) (hMcg : Structure.CG L M) (hA : Structure.FG L A)
    (aM : A ↪[L] M) (aN : A ↪[L] N) : ∃ e : M ↪[L] N, e.comp aM = aN :=
  exists_embedding_comp_eq_of_isExtensionPair hA aM aN hMcg (isExtensionPair_of_age_subset hM hN)

/-- **Rooted uniqueness.** Two countably generated structures in the same carrier universe, each
with its age in the representative class and each extending the representatives' embeddings, are
isomorphic over any finitely generated common root. -/
theorem exists_equiv_comp_eq_of_age_subset {N : Type w} [L.Structure N]
    (hM : L.age M ⊆ representativeClass F) (hN : L.age N ⊆ representativeClass F)
    (hMext : ExtendsRepresentatives F M) (hNext : ExtendsRepresentatives F N)
    (hMcg : Structure.CG L M) (hNcg : Structure.CG L N) (hA : Structure.FG L A)
    (aM : A ↪[L] M) (aN : A ↪[L] N) : ∃ e : M ≃[L] N, e.toEmbedding.comp aM = aN :=
  exists_equiv_comp_eq_of_isExtensionPair hA aM aN hMcg hNcg
    (isExtensionPair_of_age_subset hM hNext) (isExtensionPair_of_age_subset hN hMext)

/-- Relative universality for a countable source. -/
theorem exists_embedding_comp_eq_of_age_subset_of_countable [Countable M]
    (hM : L.age M ⊆ representativeClass F) (hN : ExtendsRepresentatives F N)
    (hA : Structure.FG L A) (aM : A ↪[L] M) (aN : A ↪[L] N) :
    ∃ e : M ↪[L] N, e.comp aM = aN :=
  exists_embedding_comp_eq_of_age_subset hM hN cg_of_countable hA aM aN

/-- Rooted uniqueness for countable structures. -/
theorem exists_equiv_comp_eq_of_age_subset_of_countable {N : Type w} [L.Structure N]
    [Countable M] [Countable N] (hM : L.age M ⊆ representativeClass F)
    (hN : L.age N ⊆ representativeClass F) (hMext : ExtendsRepresentatives F M)
    (hNext : ExtendsRepresentatives F N) (hA : Structure.FG L A) (aM : A ↪[L] M)
    (aN : A ↪[L] N) : ∃ e : M ≃[L] N, e.toEmbedding.comp aM = aN :=
  exists_equiv_comp_eq_of_age_subset hM hN hMext hNext cg_of_countable cg_of_countable hA aM aN

end Family

end FirstOrder.Language
