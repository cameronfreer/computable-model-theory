/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.ModelTheory.Fraisse
import Mathlib.ModelTheory.PartialEquiv
import ComputableModelTheory.ModelTheory.Computable.LimitTupleExhaustion
import ComputableModelTheory.ModelTheory.Computable.PartialMemberEmbedding

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
    L.age Z.presentation.domain = K.classSet := by
  ext A
  constructor
  · rintro ⟨hfg, ⟨f⟩⟩
    exact C.fg_mem_classSet hHP hfg f
  · intro hA
    refine ⟨K.classSet_fg hA, ?_⟩
    obtain ⟨i, ⟨e⟩⟩ := hA
    obtain ⟨s, ⟨u⟩⟩ := C.coverage hJ i
    exact ⟨(Z.stageEmbedding s).comp (u.comp e.symm.toEmbedding)⟩

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
    L.IsExtensionPair Z.presentation.domain Z.presentation.domain := by
  rw [isExtensionPair_iff_exists_embedding_closure_singleton_sup]
  intro S hS f m
  -- (a) a generating tuple of `S`, and `S` as its closure in the limit
  obtain ⟨n, tS, htS⟩ :=
    fg_iff_exists_fin_generating_family.1 (Structure.fg_def.1 ((fg_iff_structure_fg S).1 hS))
  set t : Fin n → Z.presentation.domain := fun k ↦ (tS k : Z.presentation.domain) with ht_def
  have hSt : closure L (Set.range t) = S := by
    have h1 : S = (⊤ : L.Substructure S).map S.subtype.toHom := by
      rw [← Hom.range_eq_map, range_subtype]
    rw [h1, ← htS, map_closure, ← Set.range_comp]
    rfl
  -- (b) one stage for the generators, their images, and the new point
  obtain ⟨s, hs⟩ := Z.exists_stage_list
    (List.ofFn t ++ List.ofFn (fun k ↦ f (tS k)) ++ [m])
  choose x hx hxeq using fun k ↦ hs (t k) (by simp)
  choose y hy hyeq using fun k ↦ hs (f (tS k)) (by simp)
  obtain ⟨u, hu, hueq⟩ := hs m (by simp)
  set ι := Z.stageEmbedding s with hι
  let x' : Fin n → (D.stageAt s).domain := fun k ↦ ⟨x k, hx k⟩
  let u' : (D.stageAt s).domain := ⟨u, hu⟩
  let xu : Fin (n + 1) → (D.stageAt s).domain := Fin.cons u' x'
  let mt : Fin (n + 1) → Z.presentation.domain := Fin.cons m t
  -- (c) `f` factors through the stage
  have hf_range : ∀ z : S, f z ∈ ι.toHom.range :=
    range_le_of_generators htS f ι fun k ↦ ⟨⟨y k, hy k⟩, hyeq k⟩
  let fD : S ↪[L] (D.stageAt s).domain :=
    ι.equivRange.symm.toEmbedding.comp (f.codRestrict ι.toHom.range hf_range)
  have hfD : ∀ z : S, ι (fD z) = f z := fun z ↦ by
    show ι (ι.equivRange.symm (f.codRestrict ι.toHom.range hf_range z)) = f z
    rw [← Embedding.equivRange_apply, Equiv.apply_symm_apply]
    rfl
  -- (d) the stage is a member; HP names the two generated members
  obtain ⟨i, ⟨e⟩⟩ := C.stage_iso s
  obtain ⟨a, ⟨φa⟩⟩ := hHP i n fun k ↦ e (x' k)
  obtain ⟨b, ⟨φb⟩⟩ := hHP i (n + 1) fun k ↦ e (xu k)
  have hle : closure L (Set.range fun k ↦ e (x' k)) ≤
      closure L (Set.range fun k ↦ e (xu k)) := by
    refine closure_mono ?_
    rintro _ ⟨k, rfl⟩
    exact ⟨k.succ, by simp [xu]⟩
  let g : (K.memberAt a).domain ↪[L] (K.memberAt b).domain :=
    φb.toEmbedding.comp ((inclusion hle).comp φa.symm.toEmbedding)
  -- (e) the members, read back in the stage and in the limit
  have hS_eq : closure L (Set.range fun k ↦ ι (x' k)) = S := by
    rw [show (fun k ↦ ι (x' k)) = t from funext hxeq]; exact hSt
  let eS : closure L (Set.range x') ≃[L] S :=
    (equivOfEq hS_eq).comp (closureRangeEquiv ι x')
  let eA : closure L (Set.range x') ≃[L] closure L (Set.range fun k ↦ e (x' k)) :=
    closureRangeEquiv e.toEmbedding x'
  let f'' : (K.memberAt a).domain ↪[L] (D.stageAt s).domain :=
    fD.comp (eS.toEmbedding.comp (eA.symm.toEmbedding.comp φa.symm.toEmbedding))
  -- (f) extend
  obtain ⟨s', h, -, hsq⟩ := C.extension s a b f'' g
  -- (g) the extension, returned to the limit
  have hT_eq : closure L (Set.range fun k ↦ ι (xu k)) = closure L {m} ⊔ S := by
    have hcons : (fun k ↦ ι (xu k)) = mt := by
      funext k
      refine Fin.cases ?_ (fun k ↦ ?_) k
      · simpa [xu, mt] using hueq
      · simpa [xu, mt] using hxeq k
    rw [hcons]
    show closure L (Set.range (Fin.cons m t)) = _
    rw [Fin.range_cons, closure_insert, hSt]
  let eT : closure L (Set.range xu) ≃[L] (closure L {m} ⊔ S : L.Substructure _) :=
    (equivOfEq hT_eq).comp (closureRangeEquiv ι xu)
  let eB : closure L (Set.range xu) ≃[L] closure L (Set.range fun k ↦ e (xu k)) :=
    closureRangeEquiv e.toEmbedding xu
  refine ⟨(Z.stageEmbedding s').comp
    (h.comp (φb.toEmbedding.comp (eB.toEmbedding.comp eT.symm.toEmbedding))), ?_⟩
  -- (h) it extends `f`
  refine Embedding.ext fun z ↦ ?_
  -- the point of member `a` corresponding to `z`
  set q : (K.memberAt a).domain := φa (eA (eS.symm z)) with hq
  have hgq : g q = φb (eB (eT.symm (inclusion le_sup_right z))) := by
    simp only [g, hq, Embedding.comp_apply, Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
    congr 1
    refine Subtype.ext ?_
    have hval : ((eS.symm z : closure L (Set.range x')) : (D.stageAt s).domain) =
        ((eT.symm (inclusion le_sup_right z) : closure L (Set.range xu)) :
          (D.stageAt s).domain) := by
      apply ι.injective
      have h1 : ι ((eS.symm z : closure L (Set.range x')) : (D.stageAt s).domain) =
          (z : Z.presentation.domain) := by
        rw [show eS.symm z = (closureRangeEquiv ι x').symm ((equivOfEq hS_eq).symm z) from rfl,
          closureRangeEquiv_symm_apply, equivOfEq_symm_apply]
      have h2 : ι ((eT.symm (inclusion le_sup_right z) : closure L (Set.range xu)) :
          (D.stageAt s).domain) = (z : Z.presentation.domain) := by
        rw [show eT.symm (inclusion le_sup_right z) =
          (closureRangeEquiv ι xu).symm ((equivOfEq hT_eq).symm (inclusion le_sup_right z)) from
          rfl, closureRangeEquiv_symm_apply, equivOfEq_symm_apply]
        rfl
      rw [h1, h2]
    have hincl : ∀ w : closure L (Set.range fun k ↦ e (x' k)),
        (((inclusion hle) w : closure L (Set.range fun k ↦ e (xu k))) : (K.memberAt i).domain) =
          (w : (K.memberAt i).domain) := fun _ ↦ rfl
    rw [hincl]
    show ((closureRangeEquiv e.toEmbedding x' (eS.symm z) : closure L _) : (K.memberAt i).domain) =
      ((closureRangeEquiv e.toEmbedding xu (eT.symm (inclusion le_sup_right z)) : closure L _) :
        (K.memberAt i).domain)
    rw [closureRangeEquiv_apply, closureRangeEquiv_apply, hval]
  have hf'' : f'' q = fD z := by
    simp only [f'', hq, Embedding.comp_apply, Equiv.coe_toEmbedding, Equiv.symm_apply_apply,
      Equiv.apply_symm_apply]
  have := hsq q
  rw [hgq, hf'', hfD] at this
  show f z = (Z.stageEmbedding s') (h (φb (eB (eT.symm (inclusion le_sup_right z)))))
  exact this.symm

/-- **Ultrahomogeneity**, through Mathlib: the limit is countably generated (it is countable), so
the extension pair is ultrahomogeneity. -/
theorem FraisseChainData.isUltrahomogeneous (C : FraisseChainData K Z) (hHP : K.HasHP) :
    L.IsUltrahomogeneous Z.presentation.domain :=
  (isUltrahomogeneous_iff_IsExtensionPair Structure.cg_of_countable).2 (C.isExtensionPair hHP)

/-- **Lemma 3.8, semantically**: the limit of a chain of members with the full extension property
is a Fraïssé limit of the represented class, for `K` with semantic HP and JEP. -/
theorem FraisseChainData.isFraisseLimit (C : FraisseChainData K Z) (hHP : K.HasHP)
    (hJ : K.HasJEP) : L.IsFraisseLimit K.classSet Z.presentation.domain :=
  ⟨C.isUltrahomogeneous hHP, C.age_eq hHP hJ⟩

end LimitIn

end CeStructureChainIn

end FirstOrder.Language
