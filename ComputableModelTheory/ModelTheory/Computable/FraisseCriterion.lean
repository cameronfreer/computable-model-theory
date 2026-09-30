/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.ModelTheory.Fraisse
import Mathlib.ModelTheory.PartialEquiv
import ComputableModelTheory.ModelTheory.Computable.LimitTupleExhaustion
import ComputableModelTheory.ModelTheory.Computable.PartialMemberEmbedding
import ComputableModelTheory.ModelTheory.ExtensionRichFamily
import ComputableModelTheory.ModelTheory.RepresentativeAge

/-!
# Lemma 3.8 as a semantic criterion: the limit of an extension-closed chain is a Fraïssé limit

CHMM's Lemma 3.8, in Mathlib's vocabulary: if the chain `D` has every stage isomorphic to a member
of `K`, and satisfies the **full extension property** — every embedding `f : A ↪ D_r` of a member
and every embedding `g : A ↪ B` into another member extend to some `h : B ↪ D_s`, `s ≥ r`, with
`h ∘ g = δ_{r,s} ∘ f` — then, for `K` with the semantic hereditary and joint embedding properties,
the Level-1 limit `Z.presentation.domain` is a Fraïssé limit of `K.classSet`
(`FirstOrder.Language.IsFraisseLimit`).

Everything here is semantic and classical. It consumes an already-built chain and limit and needs
no base nonemptiness witness of its own, no CHP/CJEP selectors, no infinitude certificate, and no
oracle inclusion; stages and realizers are chosen classically. The effective construction supplies
its own programs separately.

## Proof order

1. `PartialAgeIn.classSet` — the isomorphism closure of the bundled members, matching
   `ComputableAgeIn.classSet` — with membership, equivalence invariance, and finite generation.
2. **Coverage is derived**, not assumed: every member embeds into some stage, from semantic JEP and
   the extension property applied at stage `0`'s representative.
3. **Age equality**: coverage gives `classSet ⊆ age`; HP plus finite-tuple exhaustion gives
   `age ⊆ classSet` (a finitely generated substructure of the limit lives in one stage, that stage
   is a member, and HP closes).
4. **Ultrahomogeneity through Mathlib**: the adapter from chain extension and exhaustion to
   `IsExtensionPair M M` (`isExtensionPair_iff_exists_embedding_closure_singleton_sup`), then
   `isUltrahomogeneous_iff_IsExtensionPair` with countable generation from countability, and the
   `IsFraisseLimit` packaging.

Steps 3 and 4 run through the classical criterion of `ExtensionRichFamily`, applied to the stage
images `stageRange r` in the limit: they are finitely cofinal (`fgCofinal_stageRange`), the chain
data and HP make them extension rich (`FraisseChainData.extensionRich`), each is in the class
(`stageRange_mem_classSet`), and the class is hereditary (`HasHP.classSet_hereditary`). Coverage
of the class by the stages stays here, as the upper-layer JEP argument.

The square in the extension property is stated in the limit — `Z.stageEmbedding s (h (g a)) =
Z.stageEmbedding r (f a)` — which is what the criterion consumes; a square in the chain gives it
through `LimitIn.stageEmbedding_transport`.
-/

open FirstOrder Language Substructure

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-! ### Step 1: the represented class -/

namespace PartialAgeIn

variable (K : PartialAgeIn O L)

/-- The `i`-th member as a bundled structure, on its carrier subtype. -/
noncomputable def memberBundled (i : ℕ) : CategoryTheory.Bundled L.Structure :=
  ⟨(K.memberAt i).domain, inferInstance⟩

/-- **The represented class**: the isomorphism closure of the bundled members, exactly as
`ComputableAgeIn.classSet`. -/
def classSet : Set (CategoryTheory.Bundled L.Structure) :=
  {A | ∃ i, Nonempty (K.memberBundled i ≃[L] A)}

theorem memberBundled_mem_classSet (i : ℕ) : K.memberBundled i ∈ K.classSet :=
  ⟨i, ⟨Equiv.refl L _⟩⟩

theorem classSet_equiv_invariant {A B : CategoryTheory.Bundled L.Structure}
    (hA : A ∈ K.classSet) (e : A ≃[L] B) : B ∈ K.classSet := by
  obtain ⟨i, ⟨f⟩⟩ := hA
  exact ⟨i, ⟨e.comp f⟩⟩

/-- A structure isomorphic to a member's carrier is in the class. -/
theorem mem_classSet_of_equiv {A : CategoryTheory.Bundled L.Structure} {i : ℕ}
    (e : (K.memberAt i).domain ≃[L] A) : A ∈ K.classSet :=
  ⟨i, ⟨e⟩⟩

/-- **Every member is finitely generated**, by its recorded generators: the generation law says
every carrier element is a term value over them. -/
theorem memberAt_fg (i : ℕ) : Structure.FG L (K.memberAt i).domain := by
  rw [Structure.fg_iff]
  refine ⟨Set.range (K.gensView i), Set.finite_range _, top_unique fun x _ ↦ ?_⟩
  rw [mem_closure_iff_exists_term]
  obtain ⟨T, hT⟩ := exists_realize_gensView x
  refine ⟨T.relabel fun k ↦ ⟨K.gensView i k, Set.mem_range_self k⟩, ?_⟩
  rw [Term.realize_relabel]
  exact hT

theorem classSet_fg {A : CategoryTheory.Bundled L.Structure} (hA : A ∈ K.classSet) :
    Structure.FG L A := by
  obtain ⟨i, ⟨e⟩⟩ := hA
  exact (Equiv.fg_iff e).1 (K.memberAt_fg i)

/-- The **semantic** joint embedding property: any two members embed into a common member. -/
def HasJEP : Prop :=
  ∀ i j : ℕ, ∃ k : ℕ,
    Nonempty ((K.memberAt i).domain ↪[L] (K.memberAt k).domain) ∧
      Nonempty ((K.memberAt j).domain ↪[L] (K.memberAt k).domain)

end PartialAgeIn

/-! ### Substructure bookkeeping -/

namespace Substructure

variable {M : Type*} [L.Structure M]

/-- Transport along an equality of substructures. -/
noncomputable def equivOfEq {S T : L.Substructure M} (h : S = T) : S ≃[L] T := by
  subst h; exact Equiv.refl L S

@[simp] theorem equivOfEq_apply {S T : L.Substructure M} (h : S = T) (x : S) :
    (equivOfEq (L := L) h x : M) = x := by
  subst h; rfl

@[simp] theorem equivOfEq_symm_apply {S T : L.Substructure M} (h : S = T) (y : T) :
    ((equivOfEq (L := L) h).symm y : M) = y := by
  subst h; rfl

end Substructure

/-- Mapping the closure of a tuple's range along an embedding is the closure of the image tuple's
range. -/
theorem embedding_map_closure_range {M N : Type*} [L.Structure M] [L.Structure N]
    (f : M ↪[L] N) {n : ℕ} (t : Fin n → M) :
    (closure L (Set.range t)).map f.toHom = closure L (Set.range fun k ↦ f (t k)) := by
  rw [map_closure, ← Set.range_comp]
  rfl

/-- The closure of a tuple's range, carried along an embedding, as an equivalence onto the closure
of the image tuple's range. -/
noncomputable def closureRangeEquiv {M N : Type*} [L.Structure M] [L.Structure N] (f : M ↪[L] N)
    {n : ℕ} (t : Fin n → M) :
    closure L (Set.range t) ≃[L] closure L (Set.range fun k ↦ f (t k)) :=
  (equivOfEq (embedding_map_closure_range f t)).comp (f.substructureEquivMap _)

@[simp] theorem closureRangeEquiv_apply {M N : Type*} [L.Structure M] [L.Structure N]
    (f : M ↪[L] N) {n : ℕ} (t : Fin n → M) (x : closure L (Set.range t)) :
    (closureRangeEquiv f t x : N) = f x := by
  simp [closureRangeEquiv]

theorem closureRangeEquiv_symm_apply {M N : Type*} [L.Structure M] [L.Structure N]
    (f : M ↪[L] N) {n : ℕ} (t : Fin n → M) (y : closure L (Set.range fun k ↦ f (t k))) :
    f ((closureRangeEquiv f t).symm y : M) = y := by
  have := closureRangeEquiv_apply f t ((closureRangeEquiv f t).symm y)
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

/-! ### The represented class is hereditary -/

namespace PartialAgeIn

variable {K : PartialAgeIn O L}

/-- **The semantic hereditary property makes the represented class hereditary**, in Mathlib's
sense: a finitely generated structure embedding into a member is generated there by the image of
its generators, and HP names that closure as a member. -/
theorem HasHP.classSet_hereditary (hHP : K.HasHP) : Hereditary K.classSet := by
  intro A hA N hN
  obtain ⟨i, ⟨eA⟩⟩ := hA
  obtain ⟨hNfg, ⟨ι⟩⟩ := hN
  obtain ⟨n, t, ht⟩ := fg_iff_exists_fin_generating_family.1 (Structure.fg_def.1 hNfg)
  let ι' : N ↪[L] (K.memberAt i).domain := eA.symm.toEmbedding.comp ι
  obtain ⟨j, ⟨φ⟩⟩ := hHP i n fun k ↦ ι' (t k)
  exact K.mem_classSet_of_equiv (i := j)
    ((φ.comp ((closureRangeEquiv ι' t).comp ((equivOfEq ht.symm).comp topEquiv.symm))).symm)

end PartialAgeIn

/-! ### The represented class as a class of representatives -/

namespace PartialAgeIn

variable (K : PartialAgeIn O L)

/-- **The represented class is the representative class of the bundled members**, in the members'
own carrier universe. -/
theorem classSet_eq_representativeClass :
    (K.classSet : Set (CategoryTheory.Bundled.{0} L.Structure)) =
      representativeClass K.memberBundled := by
  ext A
  exact ⟨fun ⟨i, ⟨e⟩⟩ ↦ ⟨i, ⟨e.symm⟩⟩, fun ⟨i, ⟨e⟩⟩ ↦ ⟨i, ⟨e.symm⟩⟩⟩

variable {K}

/-- HP, read on substructures: every finitely generated substructure of a member is a member, up to
isomorphism. -/
theorem HasHP.exists_equiv_of_fg (hHP : K.HasHP) (i : ℕ) (S : L.Substructure (K.memberAt i).domain)
    (hS : S.FG) : ∃ j, Nonempty (S ≃[L] K.memberBundled j) := by
  obtain ⟨n, t, rfl⟩ := fg_iff_exists_fin_generating_family.1 hS
  obtain ⟨j, ⟨φ⟩⟩ := hHP i n t
  exact ⟨j, ⟨φ⟩⟩

/-- **The represented class is a Fraïssé class** (Mathlib's `IsFraisse`), given semantic HP, JEP and
amalgamation of member embeddings with a literal commuting square. -/
theorem isFraisse_classSet (hHP : K.HasHP) (hJ : K.HasJEP)
    (hAP : ∀ (i j k : ℕ) (f : K.memberBundled i ↪[L] K.memberBundled j)
      (g : K.memberBundled i ↪[L] K.memberBundled k),
      ∃ (l : ℕ) (a : K.memberBundled j ↪[L] K.memberBundled l)
        (b : K.memberBundled k ↪[L] K.memberBundled l), a.comp f = b.comp g) :
    IsFraisse (K.classSet : Set (CategoryTheory.Bundled.{0} L.Structure)) := by
  rw [classSet_eq_representativeClass]
  exact isFraisse_representativeClass K.memberBundled (fun i ↦ K.memberAt_fg i)
    hHP.exists_equiv_of_fg hJ hAP

end PartialAgeIn

/-! ### The chain hypotheses -/

namespace CeStructureChainIn

variable {E : Set (ℕ →. ℕ)} {D : CeStructureChainIn E L}

namespace LimitIn

variable (Z : D.LimitIn)

/-- **The chain hypotheses of Lemma 3.8**: every stage is a member, and the full extension
property holds, with the square read in the limit. -/
structure FraisseChainData (K : PartialAgeIn O L) (Z : D.LimitIn) : Prop where
  /-- Stage membership: input data. -/
  stage_iso : ∀ r, ∃ i, Nonempty ((D.stageAt r).domain ≃[L] (K.memberAt i).domain)
  /-- The full extension property, with the square in the limit. -/
  extension : ∀ (r i j : ℕ) (f : (K.memberAt i).domain ↪[L] (D.stageAt r).domain)
    (g : (K.memberAt i).domain ↪[L] (K.memberAt j).domain),
    ∃ (s : ℕ) (h : (K.memberAt j).domain ↪[L] (D.stageAt s).domain), r ≤ s ∧
      ∀ a, Z.stageEmbedding s (h (g a)) = Z.stageEmbedding r (f a)

variable {K : PartialAgeIn O L} {Z}

/-! ### Step 2: coverage is derived -/

/-- **Coverage**: every member embeds into some stage — from JEP with stage `0`'s representative
and the extension property. -/
theorem FraisseChainData.coverage (C : FraisseChainData K Z) (hJ : K.HasJEP) (i : ℕ) :
    ∃ s, Nonempty ((K.memberAt i).domain ↪[L] (D.stageAt s).domain) := by
  obtain ⟨i₀, ⟨e₀⟩⟩ := C.stage_iso 0
  obtain ⟨k, ⟨u⟩, ⟨v⟩⟩ := hJ i₀ i
  obtain ⟨s, h, -, -⟩ := C.extension 0 i₀ k e₀.symm.toEmbedding u
  exact ⟨s, ⟨h.comp v⟩⟩

/-! ### Step 3: age equality -/

/-- A stage tuple's closure, carried into the limit, is the closure of the limit tuple. -/
theorem closure_range_stageEmbedding (s : ℕ) {n : ℕ} (w : Fin n → (D.stageAt s).domain) :
    (closure L (Set.range w)).map (Z.stageEmbedding s).toHom =
      closure L (Set.range fun k ↦ Z.stageEmbedding s (w k)) :=
  embedding_map_closure_range _ w

/-! ### The stage images, as a family of substructures of the limit -/

variable (Z) in
/-- The image of stage `r` in the limit. -/
def stageRange (r : ℕ) : L.Substructure Z.presentation.domain :=
  (Z.stageEmbedding r).toHom.range

theorem mem_stageRange_iff {r : ℕ} {x : Z.presentation.domain} :
    x ∈ Z.stageRange r ↔ ∃ y, Z.stageEmbedding r y = x :=
  Iff.rfl

/-- **Coherence**: an earlier stage's image lies in a later one's, by transport and the limit's
coherence along it. -/
theorem stageRange_mono {r s : ℕ} (hrs : r ≤ s) : Z.stageRange r ≤ Z.stageRange s := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨z, hz, hzs⟩ := CeStructureChainIn.exists_transport_mem hrs y.2
  obtain ⟨_, heq⟩ := Z.stageEmbedding_transport hrs y.2 hz
  exact ⟨⟨z, hzs⟩, heq.symm⟩

/-- Every element of the limit lies in some stage's image. -/
theorem exists_mem_stageRange (x : Z.presentation.domain) : ∃ r, x ∈ Z.stageRange r := by
  obtain ⟨r, y, hy, heq⟩ := Z.coverage x
  exact ⟨r, ⟨y, hy⟩, heq⟩

variable (Z) in
/-- **The stage images are finitely cofinal**: they are directed and exhaust the limit. -/
theorem fgCofinal_stageRange : FGCofinal Z.stageRange :=
  fgCofinal_of_directed
    (fun r s ↦ ⟨max r s, stageRange_mono (le_max_left r s), stageRange_mono (le_max_right r s)⟩)
    Z.exists_mem_stageRange

/-- A finitely generated substructure inside a stage's image is the image of the closure of a
tuple of that stage. -/
theorem exists_stage_generators {r : ℕ} {T : L.Substructure Z.presentation.domain}
    (hT : T.FG) (hTr : T ≤ Z.stageRange r) :
    ∃ (n : ℕ) (w : Fin n → (D.stageAt r).domain),
      closure L (Set.range fun k ↦ Z.stageEmbedding r (w k)) = T := by
  obtain ⟨n, t, ht⟩ := fg_iff_exists_fin_generating_family.1 hT
  choose w hw using fun k ↦ hTr (ht ▸ subset_closure (Set.mem_range_self k) : t k ∈ T)
  exact ⟨n, w, by rw [show (fun k ↦ Z.stageEmbedding r (w k)) = t from funext hw, ht]⟩

/-! ### The represented class, read through the stage images -/

/-- Each stage's image is in the represented class. -/
theorem FraisseChainData.stageRange_mem_classSet (C : FraisseChainData K Z) (r : ℕ) :
    CategoryTheory.Bundled.of (c := L.Structure) (Z.stageRange r) ∈ K.classSet := by
  obtain ⟨i, ⟨e⟩⟩ := C.stage_iso r
  exact K.mem_classSet_of_equiv ((Z.stageEmbedding r).equivRange.comp e.symm)

/-- Every member of the represented class embeds into some stage's image: coverage, from JEP and
the extension property. -/
theorem FraisseChainData.exists_embedding_stageRange (C : FraisseChainData K Z) (hJ : K.HasJEP)
    {A : CategoryTheory.Bundled L.Structure} (hA : A ∈ K.classSet) :
    ∃ r, Nonempty (A ↪[L] Z.stageRange r) := by
  obtain ⟨i, ⟨e⟩⟩ := hA
  obtain ⟨r, ⟨u⟩⟩ := C.coverage hJ i
  exact ⟨r, ⟨(Z.stageEmbedding r).equivRange.toEmbedding.comp (u.comp e.symm.toEmbedding)⟩⟩

/-- **The chain data make the stage images extension rich.** Given finitely generated
`S ≤ T ≤` stage `r`'s image and `f : S ↪` that image: pull `S` and `T` back to generating tuples of
stage `r`, read them in stage `r`'s member, name their closures as members by HP, extend there by
the chain's extension property, and return to the limit. The receiving stage is later, but extension
richness does not ask for that. -/
theorem FraisseChainData.extensionRich (C : FraisseChainData K Z) (hHP : K.HasHP) :
    ExtensionRich Z.stageRange := by
  intro r S T hS hT hST hTr f
  set ι := Z.stageEmbedding r with hι
  -- (a) generating tuples of `S` and `T` in stage `r`
  obtain ⟨n, wS, hwS⟩ := Z.exists_stage_generators hS (hST.trans hTr)
  obtain ⟨m, wT, hwT⟩ := Z.exists_stage_generators hT hTr
  let eS : closure L (Set.range wS) ≃[L] S := (equivOfEq hwS).comp (closureRangeEquiv ι wS)
  let eT : closure L (Set.range wT) ≃[L] T := (equivOfEq hwT).comp (closureRangeEquiv ι wT)
  have hleST : closure L (Set.range wS) ≤ closure L (Set.range wT) := by
    rw [← map_le_map_iff_of_injective (f := ι.toHom) ι.injective,
      embedding_map_closure_range, embedding_map_closure_range, hwS, hwT]
    exact hST
  -- (b) the stage is a member; HP names the two generated closures
  obtain ⟨i, ⟨e⟩⟩ := C.stage_iso r
  obtain ⟨a, ⟨φa⟩⟩ := hHP i n fun k ↦ e (wS k)
  obtain ⟨b, ⟨φb⟩⟩ := hHP i m fun k ↦ e (wT k)
  let eA : closure L (Set.range wS) ≃[L] closure L (Set.range fun k ↦ e (wS k)) :=
    closureRangeEquiv e.toEmbedding wS
  let eB : closure L (Set.range wT) ≃[L] closure L (Set.range fun k ↦ e (wT k)) :=
    closureRangeEquiv e.toEmbedding wT
  have hle : closure L (Set.range fun k ↦ e (wS k)) ≤ closure L (Set.range fun k ↦ e (wT k)) := by
    refine closure_le.2 ?_
    rintro _ ⟨k, rfl⟩
    have hk := (closureRangeEquiv e.toEmbedding wT ⟨wS k, hleST (subset_closure ⟨k, rfl⟩)⟩).2
    rw [closureRangeEquiv_apply] at hk
    exact hk
  -- (c) the inclusion and `f`, as member embeddings
  let g : (K.memberAt a).domain ↪[L] (K.memberAt b).domain :=
    φb.toEmbedding.comp ((inclusion hle).comp φa.symm.toEmbedding)
  let f'' : (K.memberAt a).domain ↪[L] (D.stageAt r).domain :=
    ι.equivRange.symm.toEmbedding.comp
      (f.comp (eS.toEmbedding.comp (eA.symm.toEmbedding.comp φa.symm.toEmbedding)))
  -- (d) extend
  obtain ⟨s, h, -, hsq⟩ := C.extension r a b f'' g
  refine ⟨s, (Z.stageEmbedding s).equivRange.toEmbedding.comp
    (h.comp (φb.toEmbedding.comp (eB.toEmbedding.comp eT.symm.toEmbedding))), fun x ↦ ?_⟩
  -- (e) the point of member `a` naming `x`, and the square
  set q : (K.memberAt a).domain := φa (eA (eS.symm x)) with hq
  have hstage : ((eS.symm x : closure L (Set.range wS)) : (D.stageAt r).domain) =
      ((eT.symm (inclusion hST x) : closure L (Set.range wT)) : (D.stageAt r).domain) := by
    apply ι.injective
    have h₁ : ι ((eS.symm x : closure L (Set.range wS)) : (D.stageAt r).domain) =
        (x : Z.presentation.domain) := by
      rw [show eS.symm x = (closureRangeEquiv ι wS).symm ((equivOfEq hwS).symm x) from rfl,
        closureRangeEquiv_symm_apply, equivOfEq_symm_apply]
    have h₂ : ι ((eT.symm (inclusion hST x) : closure L (Set.range wT)) : (D.stageAt r).domain) =
        (x : Z.presentation.domain) := by
      rw [show eT.symm (inclusion hST x) =
          (closureRangeEquiv ι wT).symm ((equivOfEq hwT).symm (inclusion hST x)) from rfl,
        closureRangeEquiv_symm_apply, equivOfEq_symm_apply]
      rfl
    rw [h₁, h₂]
  have hgq : g q = φb (eB (eT.symm (inclusion hST x))) := by
    simp only [g, hq, Embedding.comp_apply, Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
    congr 1
    refine Subtype.ext ?_
    change ((closureRangeEquiv e.toEmbedding wS (eS.symm x) : closure L _) :
        (K.memberAt i).domain) =
      ((closureRangeEquiv e.toEmbedding wT (eT.symm (inclusion hST x)) : closure L _) :
        (K.memberAt i).domain)
    rw [closureRangeEquiv_apply, closureRangeEquiv_apply, hstage]
  have hf'' : ι (f'' q) = (f x : Z.presentation.domain) := by
    change ι (ι.equivRange.symm (f (eS (eA.symm (φa.symm q))))) = _
    rw [← Embedding.equivRange_apply, Equiv.apply_symm_apply, hq]
    simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  have := hsq q
  rw [hgq, hf''] at this
  change Z.stageEmbedding s (h (φb (eB (eT.symm (inclusion hST x))))) = _
  exact this

/-- **Every finitely generated substructure of the limit is a member**, up to isomorphism: its
generators lie in one stage, that stage is a member, and HP closes. -/
theorem FraisseChainData.fg_mem_classSet (C : FraisseChainData K Z) (hHP : K.HasHP)
    {A : CategoryTheory.Bundled L.Structure} (hA : Structure.FG L A)
    (f : A ↪[L] Z.presentation.domain) : A ∈ K.classSet := by
  obtain ⟨n, t, ht⟩ := fg_iff_exists_fin_generating_family.1 (Structure.fg_def.1 hA)
  obtain ⟨s, w, hw, heq⟩ := Z.exists_stage_tuple fun k ↦ f (t k)
  obtain ⟨i, ⟨e⟩⟩ := C.stage_iso s
  let w' : Fin n → (D.stageAt s).domain := fun k ↦ ⟨w k, hw k⟩
  obtain ⟨j, ⟨φ⟩⟩ := hHP i n fun k ↦ e (w' k)
  refine K.mem_classSet_of_equiv (i := j) ?_
  -- A ≃ ⊤ = closure (range t) ≃ closure (range (f ∘ t)) = closure (range (stageEmb ∘ w'))
  --   ≃ closure (range w') ≃ closure (range (e ∘ w')) ≃ member j
  have h1 : closure L (Set.range fun k ↦ f (t k)) =
      closure L (Set.range fun k ↦ Z.stageEmbedding s (w' k)) := by
    congr 1; ext x; simp only [Set.mem_range]; exact exists_congr fun k ↦ by rw [heq k]
  have φ' : closure L (Set.range fun k ↦ e.toEmbedding (w' k)) ≃[L] (K.memberAt j).domain := φ
  -- composed right to left
  exact (φ'.comp ((closureRangeEquiv e.toEmbedding w').comp
    ((closureRangeEquiv (Z.stageEmbedding s) w').symm.comp ((equivOfEq h1).comp
      ((closureRangeEquiv f t).comp ((equivOfEq ht.symm).comp topEquiv.symm)))))).symm

/-- **Age equality.** -/
theorem FraisseChainData.age_eq (C : FraisseChainData K Z) (hHP : K.HasHP) (hJ : K.HasJEP) :
    L.age Z.presentation.domain = K.classSet :=
  age_eq_of_fgCofinal K.classSet hHP.classSet_hereditary C.stageRange_mem_classSet
    (fun _ hA ↦ C.exists_embedding_stageRange hJ hA) (fun _ hA ↦ K.classSet_fg hA)
    (fgCofinal_stageRange Z)

/-! ### Step 4: the extension pair, ultrahomogeneity, and the packaging -/

/-- An embedding out of a substructure generated by a tuple whose image lands in the range of
another embedding factors through it: its whole range does, because the range is closed under
term realization. -/
theorem range_le_of_generators {M N : Type*} [L.Structure M] [L.Structure N]
    {S : L.Substructure M} {n : ℕ} {t : Fin n → S} (ht : closure L (Set.range t) = ⊤)
    (f : S ↪[L] M) (ι : N ↪[L] M) (hf : ∀ k, f (t k) ∈ ι.toHom.range) :
    ∀ z : S, f z ∈ ι.toHom.range := by
  intro z
  have hz : z ∈ (⊤ : L.Substructure S) := mem_top z
  rw [← ht, mem_closure_iff_exists_term] at hz
  obtain ⟨T, rfl⟩ := hz
  rw [← HomClass.realize_term (g := f)]
  refine Term.realize_mem T _ fun a ↦ ?_
  obtain ⟨k, hk⟩ := a.2
  show f a ∈ _
  rw [← hk]
  exact hf k

/-- **The extension-pair adapter.** A finitely generated substructure `S` of the limit, an
embedding `f : S ↪ M`, and a point `m`: everything relevant lies in one stage; the stage is a
member; HP names the members generated by the preimages of `S`'s generators, without and with the
preimage of `m`; `f` factors through the stage; the chain's extension property extends; and the
stage injection returns to the limit. -/
theorem FraisseChainData.isExtensionPair (C : FraisseChainData K Z) (hHP : K.HasHP) :
    L.IsExtensionPair Z.presentation.domain Z.presentation.domain :=
  isExtensionPair_of_extensionRich (fgCofinal_stageRange Z) (C.extensionRich hHP)

/-- **Ultrahomogeneity**, through Mathlib: the limit is countably generated (it is countable), so
the extension pair is ultrahomogeneity. -/
theorem FraisseChainData.isUltrahomogeneous (C : FraisseChainData K Z) (hHP : K.HasHP) :
    L.IsUltrahomogeneous Z.presentation.domain :=
  isUltrahomogeneous_of_extensionRich Structure.cg_of_countable (fgCofinal_stageRange Z)
    (C.extensionRich hHP)

/-- **Lemma 3.8, semantically**: the limit of a chain of members with the full extension property
is a Fraïssé limit of the represented class, for `K` with semantic HP and JEP. -/
theorem FraisseChainData.isFraisseLimit (C : FraisseChainData K Z) (hHP : K.HasHP)
    (hJ : K.HasJEP) : L.IsFraisseLimit K.classSet Z.presentation.domain :=
  isFraisseLimit_of_extensionRich K.classSet (fgCofinal_stageRange Z) (C.extensionRich hHP)
    hHP.classSet_hereditary C.stageRange_mem_classSet
    (fun _ hA ↦ C.exists_embedding_stageRange hJ hA) (fun _ hA ↦ K.classSet_fg hA)

end LimitIn

end CeStructureChainIn

end FirstOrder.Language
