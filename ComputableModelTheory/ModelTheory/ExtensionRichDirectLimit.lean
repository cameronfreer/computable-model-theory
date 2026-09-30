/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.ExtensionRichFamily

/-! # Extension-rich direct limits

Finitely generated embeddings into a directed limit factor through a stage.
If finite partial embeddings between stages extend to whole-source embeddings
at later target stages, the limit is an extension pair with itself. Countable
generation then gives ultrahomogeneity. The transition maps are embeddings,
not required to be inclusions. No carrier is assumed nonempty.

This is a criterion for a supplied coherent system, not a fair-chain existence
theorem. It states the finite extension squares that such a construction must
supply, independently of any effective presentation or infinitary language.
-/

universe u v w z

namespace FirstOrder.Language

open FirstOrder FirstOrder.Language FirstOrder.Language.Substructure

variable {L : Language.{u, v}} {ι : Type z} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  (G : ι → Type w) [∀ i, L.Structure (G i)]
  (f : ∀ i j, i ≤ j → G i ↪[L] G j) [DirectedSystem G (fun i j h => f i j h)]

/-- The canonical stage images are monotone, even when the connecting maps
are not inclusions. -/
theorem directLimit_range_mono {i j : ι} (hij : i ≤ j) :
    (DirectLimit.of L ι G f i).toHom.range ≤ (DirectLimit.of L ι G f j).toHom.range := by
  rintro _ ⟨x, rfl⟩
  exact ⟨f i j hij x, DirectLimit.of_f⟩

/-- Every finitely generated substructure of the limit lies in a stage image. -/
theorem fgCofinal_directLimit :
    FGCofinal (fun i => (DirectLimit.of L ι G f i).toHom.range) := by
  apply fgCofinal_of_directed
  · intro i j
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    exact ⟨k, directLimit_range_mono G f hik, directLimit_range_mono G f hjk⟩
  · intro x
    obtain ⟨i, y, rfl⟩ := DirectLimit.exists_of x
    exact ⟨i, ⟨y, rfl⟩⟩

/-- An embedding of a finitely generated structure factors literally through
one canonical stage embedding. Its carrier universe is independent of the system. -/
theorem exists_factor_directLimit {A : Type*} [L.Structure A]
    (hA : Structure.FG L A) (e : A ↪[L] Language.DirectLimit G f) :
    ∃ (i : ι) (g : A ↪[L] G i), (DirectLimit.of L ι G f i).comp g = e := by
  obtain ⟨i, hi⟩ := fgCofinal_directLimit G f e.toHom.range (hA.range e.toHom)
  let g := (DirectLimit.of L ι G f i).equivRange.symm.toEmbedding.comp
    (e.codRestrict _ (fun a => hi (Hom.mem_range_self e.toHom a)))
  refine ⟨i, g, ?_⟩
  ext a
  exact congrArg Subtype.val ((DirectLimit.of L ι G f i).equivRange.apply_symm_apply
    ⟨e a, hi (Hom.mem_range_self e.toHom a)⟩)

/-- A countable system of countable carriers has countable limit, without
countability assumptions on the signature. -/
theorem countable_directLimit [Countable ι] [∀ i, Countable (G i)] :
    Countable (Language.DirectLimit G f) := by
  apply Function.Surjective.countable
    (f := fun x : Σ i, G i => DirectLimit.of L ι G f x.1 x.2)
  intro x
  obtain ⟨i, y, rfl⟩ := DirectLimit.exists_of x
  exact ⟨⟨i, y⟩, rfl⟩

/-- Every finite partial map between stages extends to the whole source stage
at a later target stage. Only the target connecting map is prescribed. -/
def AmalgamationRich : Prop :=
  ∀ i j (S : L.Substructure (G i)), S.FG → ∀ e : S ↪[L] G j,
    ∃ (k : ι) (hjk : j ≤ k) (g : G i ↪[L] G k),
      g.comp S.subtype = (f j k hjk).comp e

/-- Stage amalgamation squares imply the unrestricted finite extension property
in the limit. No countability or finite generation of the stages is needed. -/
theorem isExtensionPair_directLimit (hrich : AmalgamationRich G f) :
    L.IsExtensionPair (Language.DirectLimit G f) (Language.DirectLimit G f) := by
  rw [isExtensionPair_iff_exists_embedding_closure_singleton_sup]
  intro S hS e x
  let T := closure L {x} ⊔ S
  have hT : T.FG := (fg_closure_singleton x).sup hS
  obtain ⟨i, t, _⟩ := exists_factor_directLimit G f
    (T.fg_iff_structure_fg.mp hT) T.subtype
  obtain ⟨j, s, hs⟩ := exists_factor_directLimit G f
    (S.fg_iff_structure_fg.mp hS) e
  let a : S ↪[L] G i := t.comp (inclusion (show S ≤ T from le_sup_right))
  obtain ⟨k, hjk, g, hg⟩ := hrich i j a.toHom.range
    ((S.fg_iff_structure_fg.mp hS).range a.toHom)
    (s.comp a.equivRange.symm.toEmbedding)
  refine ⟨(DirectLimit.of L ι G f k).comp (g.comp t), ?_⟩
  ext y
  have hy := Embedding.ext_iff.mp hg (a.equivRange y)
  have hy' : g (a y) = f j k hjk (s y) := by
    simpa only [Embedding.comp_apply, Substructure.coe_subtype, Embedding.equivRange_apply,
      Language.Equiv.coe_toEmbedding, Language.Equiv.symm_apply_apply] using hy
  change e y = DirectLimit.of L ι G f k (g (a y))
  rw [hy', DirectLimit.of_f]
  exact (Embedding.ext_iff.mp hs y).symm

/-- A countably indexed, countably generated system satisfying the stage
extension squares has an ultrahomogeneous direct limit. -/
theorem isUltrahomogeneous_directLimit [Countable ι]
    (hcg : ∀ i, Structure.CG L (G i)) (hrich : AmalgamationRich G f) :
    L.IsUltrahomogeneous (Language.DirectLimit G f) :=
  (isUltrahomogeneous_iff_IsExtensionPair (DirectLimit.cg f hcg)).mpr
    (isExtensionPair_directLimit G f hrich)

section Sequence

variable {G : ℕ → Type w} [∀ i, L.Structure (G i)]
  (f : ∀ i j, i ≤ j → G i ↪[L] G j) [DirectedSystem G (fun i j h => f i j h)]
  (K : Set (CategoryTheory.Bundled.{w} L.Structure))

/-- The whole-stage extension property of a Fraïssé sequence. Every embedding
of a stage into a member of the class is completed by a later transition map. -/
def SequenceExtension : Prop :=
  ∀ i (N : CategoryTheory.Bundled.{w} L.Structure), N ∈ K →
    ∀ e : G i ↪[L] N, ∃ (j : ℕ) (hij : i ≤ j) (g : N ↪[L] G j),
      g.comp e = f i j hij

omit [DirectedSystem G (fun i j h => f i j h)] in
/-- AP turns whole-stage extension into the partial-map squares used by the
direct-limit criterion. Hereditary closure supplies the common finite root. -/
theorem amalgamationRich_of_sequenceExtension
    (hstage : ∀ i, (⟨G i, inferInstance⟩ : CategoryTheory.Bundled L.Structure) ∈ K)
    (hhp : Hereditary K) (hap : Amalgamation K) (hext : SequenceExtension f K) :
    AmalgamationRich G f := by
  intro i j S hS e
  have hSK : (⟨S, inferInstance⟩ : CategoryTheory.Bundled L.Structure) ∈ K :=
    hhp _ (hstage i) ⟨S.fg_iff_structure_fg.mp hS, ⟨S.subtype⟩⟩
  obtain ⟨N, a, b, hN, hab⟩ := hap _ _ _ S.subtype e hSK (hstage i) (hstage j)
  obtain ⟨k, hjk, g, hg⟩ := hext j N hN b
  refine ⟨k, hjk, g.comp a, ?_⟩
  ext x
  have hx := congrArg (fun t : S ↪[L] N => g (t x)) hab
  have hy := Embedding.ext_iff.mp hg (e x)
  exact hx.trans hy

/-- Stage membership and coverage identify the age; this needs HP, not AP. -/
theorem age_directLimit_eq
    (hstage : ∀ i, (⟨G i, inferInstance⟩ : CategoryTheory.Bundled L.Structure) ∈ K)
    (hhp : Hereditary K) (hfg : ∀ N ∈ K, Structure.FG L N)
    (hcover : ∀ N ∈ K, ∃ i, Nonempty (N ↪[L] G i)) :
    L.age (Language.DirectLimit G f) = K := by
  rw [age_directLimit G f]
  apply Set.Subset.antisymm
  · intro N hN
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hN
    exact hhp _ (hstage i) hi
  · intro N hN
    obtain ⟨i, hi⟩ := hcover N hN
    exact Set.mem_iUnion.mpr ⟨i, hfg N hN, hi⟩

/-- A supplied Fraïssé sequence has a Fraïssé limit. This packages its semantic
conclusion, not the existence of the sequence. -/
theorem isFraisseLimit_directLimit [Countable (Σ n, L.Functions n)]
    [Countable (Language.DirectLimit G f)]
    (hstage : ∀ i, (⟨G i, inferInstance⟩ : CategoryTheory.Bundled L.Structure) ∈ K)
    (hhp : Hereditary K) (hap : Amalgamation K) (hfg : ∀ N ∈ K, Structure.FG L N)
    (hcover : ∀ N ∈ K, ∃ i, Nonempty (N ↪[L] G i))
    (hext : SequenceExtension f K) : IsFraisseLimit K (Language.DirectLimit G f) where
  ultrahomogeneous := isUltrahomogeneous_directLimit G f (fun i => (hfg _ (hstage i)).cg)
    (amalgamationRich_of_sequenceExtension f K hstage hhp hap hext)
  age := age_directLimit_eq f K hstage hhp hfg hcover

end Sequence

end FirstOrder.Language
