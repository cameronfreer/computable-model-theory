/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.ModelTheory.Fraisse

/-!
# Extension-rich families of substructures

A classical criterion for ultrahomogeneity and for being a Fraïssé limit, phrased for an arbitrary
family `U : I → L.Substructure M` of substructures of one structure `M`:

* `FGCofinal U`: every finitely generated substructure lies in some member of the family;
* `ExtensionRich U`: an embedding of a finitely generated `S ≤ T ≤ U i` into `U i` extends, along
  `S ≤ T`, to an embedding of `T` into some member `U j`, with the square commuting in `M`.

Under cofinality, extension richness is equivalent to ultrahomogeneity of a countably generated
`M` (`extensionRich_iff_isUltrahomogeneous`); the forward half gives the self-extension pair with no
countability at all (`isExtensionPair_of_extensionRich`). The age of `M` is the union of the ages
of the members (`age_eq_iUnion_of_fgCofinal`), and is identified with a hereditary class that
contains the members and covers its own elements (`age_eq_of_fgCofinal`).

**What is not assumed.** No order on `I`: the receiving member need not contain the original one.
The members need not be finitely generated. The carrier may be empty. Nothing effective — no
language coding, presentation, or oracle — appears; this file imports only
`Mathlib.ModelTheory.Fraisse`, and is meant to sit below every computable layer that uses it.

The proofs are Mathlib's: the forward direction goes through
`isExtensionPair_iff_exists_embedding_closure_singleton_sup` and
`isUltrahomogeneous_iff_IsExtensionPair`, and the converse restricts an automorphism. No
back-and-forth argument is written here.
-/

universe u v w z

namespace FirstOrder.Language

open Substructure CategoryTheory

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] {I : Type z}

section Family

variable (U : I → L.Substructure M)

/-- **Finite cofinality**: every finitely generated substructure lies in some member. -/
def FGCofinal : Prop :=
  ∀ S : L.Substructure M, S.FG → ∃ i, S ≤ U i

/-- **Extension richness**: an embedding of a finitely generated `S ≤ T ≤ U i` into `U i` extends
along `S ≤ T` to an embedding of `T` into some member `U j`, the square commuting in `M`. -/
def ExtensionRich : Prop :=
  ∀ (i : I) (S T : L.Substructure M), S.FG → T.FG →
    ∀ (hST : S ≤ T), T ≤ U i → ∀ f : S ↪[L] U i,
      ∃ (j : I) (g : T ↪[L] U j),
        ∀ a : S, (g (Substructure.inclusion hST a) : M) = (f a : M)

variable {U}

/-- **The self-extension pair.** No countability, and no nonemptiness. -/
theorem isExtensionPair_of_extensionRich (hcof : FGCofinal U) (hrich : ExtensionRich U) :
    L.IsExtensionPair M M := by
  refine isExtensionPair_iff_exists_embedding_closure_singleton_sup.2 fun S hS f m ↦ ?_
  have hT : (closure L {m} ⊔ S).FG := (fg_closure_singleton m).sup hS
  obtain ⟨i, hi⟩ := hcof _ (hT.sup (((S.fg_iff_structure_fg).1 hS).range f.toHom))
  have hTi : closure L {m} ⊔ S ≤ U i := le_sup_left.trans hi
  have hfi : ∀ x, f x ∈ U i := fun x ↦ hi (le_sup_right (a := closure L {m} ⊔ S) ⟨x, rfl⟩)
  obtain ⟨j, g, hg⟩ := hrich i S _ hS hT le_sup_right hTi (Embedding.codRestrict (U i) f hfi)
  refine ⟨(U j).subtype.comp g, ?_⟩
  ext x
  exact (hg x).symm

/-- **Ultrahomogeneity**, for a countably generated structure. -/
theorem isUltrahomogeneous_of_extensionRich (hCG : Structure.CG L M) (hcof : FGCofinal U)
    (hrich : ExtensionRich U) : L.IsUltrahomogeneous M :=
  (isUltrahomogeneous_iff_IsExtensionPair hCG).2 (isExtensionPair_of_extensionRich hcof hrich)

/-- **The converse**: under cofinality, ultrahomogeneity gives extension richness. No countable
generation is needed in this direction: extend to an automorphism, restrict it to `T`, and place
its finitely generated image in a member. -/
theorem extensionRich_of_isUltrahomogeneous (hcof : FGCofinal U)
    (hU : L.IsUltrahomogeneous M) : ExtensionRich U := by
  intro i S T hS hT hST _ f
  obtain ⟨σ, hσ⟩ := hU S hS ((U i).subtype.comp f)
  obtain ⟨j, hj⟩ := hcof _ (Substructure.FG.map σ.toHom hT)
  have hmem : ∀ x : T, σ.toEmbedding.comp T.subtype x ∈ U j := fun x ↦ hj ⟨x, x.2, rfl⟩
  refine ⟨j, Embedding.codRestrict (U j) (σ.toEmbedding.comp T.subtype) hmem, fun a ↦ ?_⟩
  have := DFunLike.congr_fun hσ a
  exact this.symm

/-- **The equivalence**, under cofinality and countable generation. -/
theorem extensionRich_iff_isUltrahomogeneous (hcof : FGCofinal U) (hCG : Structure.CG L M) :
    ExtensionRich U ↔ L.IsUltrahomogeneous M :=
  ⟨isUltrahomogeneous_of_extensionRich hCG hcof, extensionRich_of_isUltrahomogeneous hcof⟩

/-- **Directed exhaustion gives cofinality**, over an inhabited index type. The inhabitation is
needed: on an empty carrier, pointwise coverage holds for any family, including the empty one. -/
theorem fgCofinal_of_directed [Nonempty I] (hdir : Directed (· ≤ ·) U)
    (hcov : ∀ x : M, ∃ i, x ∈ U i) : FGCofinal U := by
  classical
  intro S hS
  obtain ⟨s, hs, rfl⟩ := Substructure.fg_def.1 hS
  choose idx hidx using hcov
  obtain ⟨k, hk⟩ := hdir.finset_le (hs.toFinset.image idx)
  refine ⟨k, closure_le.2 fun x hx ↦ hk (idx x) ?_ (hidx x)⟩
  exact Finset.mem_image.2 ⟨x, hs.mem_toFinset.2 hx, rfl⟩

/-- **The age is the union of the members' ages.** Only cofinality is used. -/
theorem age_eq_iUnion_of_fgCofinal (hcof : FGCofinal U) :
    L.age M = ⋃ i, L.age (U i) := by
  ext N
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨hN, ⟨e⟩⟩
    obtain ⟨i, hi⟩ := hcof _ (hN.range e.toHom)
    exact ⟨i, hN, ⟨Embedding.codRestrict (U i) e fun x ↦ hi ⟨x, rfl⟩⟩⟩
  · rintro ⟨i, hN, ⟨e⟩⟩
    exact ⟨hN, ⟨(U i).subtype.comp e⟩⟩

/-- **The age, identified with a class**: a hereditary class of finitely generated structures
containing every member and covering its own elements. No joint embedding property is assumed —
coverage is supplied directly. -/
theorem age_eq_of_fgCofinal (K : Set (Bundled.{w} L.Structure)) (hK : Hereditary K)
    (hstage : ∀ i, Bundled.of (c := L.Structure) (U i) ∈ K)
    (hcov : ∀ N ∈ K, ∃ i, Nonempty (N ↪[L] U i))
    (hfg : ∀ N ∈ K, Structure.FG L N) (hcof : FGCofinal U) : L.age M = K := by
  rw [age_eq_iUnion_of_fgCofinal hcof]
  ext N
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hN⟩
    exact hK _ (hstage i) hN
  · intro hN
    obtain ⟨i, he⟩ := hcov N hN
    exact ⟨i, hfg N hN, he⟩

/-- **A Fraïssé limit**, packaged with Mathlib's interface: cofinality, extension richness, and the
age hypotheses of `age_eq_of_fgCofinal`. -/
theorem isFraisseLimit_of_extensionRich [Countable (Σ n, L.Functions n)] [Countable M]
    (K : Set (Bundled.{w} L.Structure)) (hcof : FGCofinal U) (hrich : ExtensionRich U)
    (hK : Hereditary K) (hstage : ∀ i, Bundled.of (c := L.Structure) (U i) ∈ K)
    (hcov : ∀ N ∈ K, ∃ i, Nonempty (N ↪[L] U i)) (hfg : ∀ N ∈ K, Structure.FG L N) :
    L.IsFraisseLimit K M :=
  ⟨isUltrahomogeneous_of_extensionRich Structure.cg_of_countable hcof hrich,
    age_eq_of_fgCofinal K hK hstage hcov hfg hcof⟩

end Family

end FirstOrder.Language
