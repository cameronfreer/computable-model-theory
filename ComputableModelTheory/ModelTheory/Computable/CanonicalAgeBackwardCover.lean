/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.GeneratedImageIso
import ComputableModelTheory.ModelTheory.Computable.CeStructureOmegaTuple
import ComputableModelTheory.ModelTheory.Computable.AgeChain

/-!
# The backward cover `K → 𝕂_𝒟`

The first of the two covers of CHMM Theorem 2.10(⇐). Every member of `K` embeds into the ω-limit of
its own CJEP chain — cofinally, by construction of the schedule — and the generated-image
constructor turns that embedding into an isomorphism onto a canonical-age member. Nothing here
proves a structure law or a compatibility statement: both come from the constructor.

**The base oracle is enforced by the types, not by discipline.** `RepresentationCoverIn E A B` takes
`A` and `B` at *one* family oracle. The chain and its limit live at the selector's oracle, so
`𝕂_𝒟` of the limit is a `PartialAgeIn` at that oracle while `K` is one at its own. There is no
cover between them unless the two agree, so this file fixes the selector at `O` and the eventual
oracle lift is a separate result rather than a hypothesis that could be quietly relaxed.

**The guard is load-bearing.** `applyPotentialPart` has no exact-domain theorem — by design, since
the search that drives it may halt on codes naming nothing — but
`UniformEmbeddingIntoIn.map_dom` is an *iff*, because `PartialCeIsoIn.toFun_dom` is. Prefixing
`K.idFun`, whose domain law is an iff, repairs exactly that: a successful composite proves the guard
halted, hence source membership, whatever the later partial programs would have done on their own.
The bind tree is written in the association its recursiveness proof follows.

The carrier crossing below is **public and shared**: constructions on the family side land in
`K.memberAt (cjepSchedule … n)`, while the limit's stage embeddings expect `(cjepChain …).stageAt n`.
Same carrier, same stored structure, different subtype types. The forward cover makes the same
crossing in the opposite direction and should use this API rather than repeat it.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-! ### The carrier crossing

`PartialCePresentationIn.toCeDomainEquiv` — the generic crossing between the two presentation
layers — lives with `eqDomainEquiv` in `PartialAgeSemantics`; only the schedule-level instance is
here. Both are the identity on values. -/

namespace PartialAgeIn

variable {K : PartialAgeIn O L} {sel : ℕ → ℕ → PartialJointEmbeddingData} {baseIdx : ℕ}
variable {hne : ∀ n, (K.domainAt (cjepSchedule sel baseIdx n)).Nonempty} {hOE : O ⊆ E}

/-- **The scheduled-member carrier equivalence.** Totalizing a scheduled member changes neither its
carrier (`scheduledStage_domain`) nor its stored structure, so the family-side carrier and the
chain-stage carrier are the same thing presented at two layers. The crossing both covers make. -/
noncomputable def scheduledStageEquiv (n : ℕ) :
    (K.memberAt (cjepSchedule sel baseIdx n)).domain ≃[L]
      (scheduledStage K sel baseIdx hne hOE n).domain :=
  PartialCePresentationIn.toCeDomainEquiv rfl (scheduledStage_domain n)

@[simp]
theorem scheduledStageEquiv_coe (n : ℕ)
    (x : (K.memberAt (cjepSchedule sel baseIdx n)).domain) :
    ((scheduledStageEquiv (hne := hne) (hOE := hOE) n x :
      (scheduledStage K sel baseIdx hne hOE n).domain) : ℕ) = (x : ℕ) :=
  rfl

end PartialAgeIn

/-! ### The cofinal embedding into the ω-limit

The base oracle throughout: `E := O`, forced by `RepresentationCoverIn`'s signature. -/

namespace PartialAgeIn

/-- The chain of the schedule, at the base oracle. Every hypothesis is a real argument rather than
a section variable, so nothing is silently dropped from the signature. -/
noncomputable def selfChain (K : PartialAgeIn O L)
    (sel : ℕ → ℕ → PartialJointEmbeddingData) (baseIdx : ℕ)
    (hne : ∀ n, (K.domainAt (cjepSchedule sel baseIdx n)).Nonempty)
    (hspec : K.JointSpec sel)
    (hsel : ComputableIn O fun p : ℕ × ℕ ↦ sel p.1 p.2) : CeStructureChainIn O L :=
  cjepChain K sel baseIdx hne (Set.Subset.refl O) hspec hsel

@[simp] theorem selfChain_stageAt (K : PartialAgeIn O L)
    (sel : ℕ → ℕ → PartialJointEmbeddingData) (baseIdx : ℕ)
    (hne : ∀ n, (K.domainAt (cjepSchedule sel baseIdx n)).Nonempty)
    (hspec : K.JointSpec sel)
    (hsel : ComputableIn O fun p : ℕ × ℕ ↦ sel p.1 p.2) (n : ℕ) :
    (selfChain K sel baseIdx hne hspec hsel).stageAt n =
      scheduledStage K sel baseIdx hne (Set.Subset.refl O) n :=
  rfl

/-- Its uniform stage evaluators, so Lemma 2.9 applies. -/
theorem selfChain_uniformEvaluators (K : PartialAgeIn O L)
    (sel : ℕ → ℕ → PartialJointEmbeddingData) (baseIdx : ℕ)
    (hne : ∀ n, (K.domainAt (cjepSchedule sel baseIdx n)).Nonempty)
    (hspec : K.JointSpec sel)
    (hsel : ComputableIn O fun p : ℕ × ℕ ↦ sel p.1 p.2) :
    (selfChain K sel baseIdx hne hspec hsel).UniformEvaluatorsIn :=
  cjepChain_uniformEvaluators K sel baseIdx hne (Set.Subset.refl O) hspec hsel

variable {K : PartialAgeIn O L} {sel : ℕ → ℕ → PartialJointEmbeddingData} {baseIdx : ℕ}

/-- The realizer of the cofinality leg: member `n` embeds into stage `n + 1`. Noncomputable —
`PartialIsEmbedding` is an existential — which is exactly why the program below is carried
separately. -/
noncomputable def cofinalEmbedding (hspec : K.JointSpec sel) (baseIdx : ℕ) (n : ℕ) :
    (K.memberAt n).domain ↪[L] (K.memberAt (cjepSchedule sel baseIdx (n + 1))).domain :=
  (cofinalData_partialIsEmbedding (baseIdx := baseIdx) hspec n).choose

theorem cofinalEmbedding_mem_applyPotentialPart (hspec : K.JointSpec sel) (baseIdx : ℕ)
    {n x : ℕ} (hx : x ∈ K.domainAt n) :
    ((cofinalEmbedding hspec baseIdx n ⟨x, hx⟩ :
        (K.memberAt (cjepSchedule sel baseIdx (n + 1))).domain) : ℕ)
      ∈ K.applyPotentialPart (cofinalData sel baseIdx n) x :=
  applyPotentialPart_mem_realizer
    (cofinalData_partialIsEmbedding (baseIdx := baseIdx) hspec n).choose_spec hx

variable {hne : ∀ n, (K.domainAt (cjepSchedule sel baseIdx n)).Nonempty}
variable {hspec : K.JointSpec sel} {hsel : ComputableIn O fun p : ℕ × ℕ ↦ sel p.1 p.2}
variable (Z : (selfChain K sel baseIdx hne hspec hsel).LimitIn)
variable (cert : Z.presentation.InfinitudeCertificate)

/-- **The ω-limit of the chain, as an all-ℕ computable structure at the base oracle.** -/
noncomputable def limitStructure : ComputableStructureIn O L :=
  Z.omegaStructure cert

@[simp] theorem limitStructure_inst : (limitStructure Z cert).inst = Z.presentation.rankStr :=
  rfl

/-- **The semantic embedding of member `n` into the ω-limit**: the cofinal realizer, the carrier
crossing at stage `n + 1`, and the recoded stage embedding. -/
noncomputable def omegaEmbedding (n : ℕ) :
    @Language.Embedding L (K.memberAt n).domain ℕ _ (limitStructure Z cert).inst :=
  letI : L.Structure ℕ := Z.presentation.rankStr
  (Z.omegaStageEmbedding (n + 1)).comp
    ((scheduledStageEquiv (hne := hne) (hOE := Set.Subset.refl O) (n + 1)).toEmbedding.comp
      (cofinalEmbedding hspec baseIdx n))

/-- **The program, guarded.** The first bind is what makes the domain exact: any successful
composite proves `idFun` halted, hence source membership, whatever the later partial programs would
have done on their own. Written in the association its recursiveness proof follows. -/
noncomputable def omegaMap (n : ℕ) : ℕ →. ℕ :=
  fun x ↦ (K.idFun (n, x)).bind fun x' ↦
    (K.applyPotentialPart (cofinalData sel baseIdx n) x').bind fun y ↦
      Z.rankStageMap (n + 1) y

/-- **The two sides agree.** Each of the three stages contributes one membership: the guard returns
its input, the cofinal realizer is a value of `applyPotentialPart`, and the recoded stage embedding
is a value of `rankStageMap`. -/
theorem omegaEmbedding_mem_omegaMap (n : ℕ) (x : (K.memberAt n).domain) :
    omegaEmbedding Z cert n x ∈ omegaMap Z n (x : ℕ) := by
  refine Part.mem_bind_iff.2 ⟨(x : ℕ), K.mem_idFun.2 ⟨rfl, x.2⟩, ?_⟩
  refine Part.mem_bind_iff.2
    ⟨((cofinalEmbedding hspec baseIdx n x :
        (K.memberAt (cjepSchedule sel baseIdx (n + 1))).domain) : ℕ),
      cofinalEmbedding_mem_applyPotentialPart hspec baseIdx x.2, ?_⟩
  exact Z.omegaStageEmbedding_apply_mem (n + 1)
    (scheduledStageEquiv (hne := hne) (hOE := Set.Subset.refl O) (n + 1)
      (cofinalEmbedding hspec baseIdx n x))

/-- **The guard alone gives the hard direction**, with no certificate and no fact about the two
programs it precedes: a successful composite proves `K.idFun` halted, hence source membership. This
is what an off-carrier input runs into, whatever `applyPotentialPart` or `rankStageMap` would have
done on it. -/
theorem mem_domainAt_of_omegaMap_dom {n x : ℕ} (h : (omegaMap Z n x).Dom) : x ∈ K.domainAt n := by
  obtain ⟨y, hy⟩ := Part.dom_iff_mem.1 h
  obtain ⟨x', hx', -⟩ := Part.mem_bind_iff.1 hy
  exact (K.mem_idFun.1 hx').2

include cert in
/-- **Exact domain.** The `←` direction is on-domain halting, from the cofinal realizer and the
bridge; the `→` direction is the guard, and nothing else. -/
theorem omegaMap_dom (n x : ℕ) : (omegaMap Z n x).Dom ↔ x ∈ K.domainAt n := by
  refine ⟨mem_domainAt_of_omegaMap_dom Z, fun hx ↦ ?_⟩
  exact Part.dom_iff_mem.2 ⟨_, omegaEmbedding_mem_omegaMap Z cert n ⟨x, hx⟩⟩

/-- Uniformly partial recursive in the index. -/
theorem omegaMap_uniform :
    RecursiveIn O fun p : ℕ × ℕ ↦ omegaMap Z p.1 p.2 := by
  have h₁ : RecursiveIn O fun p : ℕ × ℕ ↦ K.idFun (p.1, p.2) := K.idFun_recursiveIn
  have h₂ : RecursiveIn O fun q : (ℕ × ℕ) × ℕ ↦
      K.applyPotentialPart (cofinalData sel baseIdx q.1.1) q.2 :=
    RecursiveIn.comp (O := O) (α := (ℕ × ℕ) × ℕ) (β := PotentialEmbeddingData × ℕ) (σ := ℕ)
      (f := fun r : PotentialEmbeddingData × ℕ ↦ K.applyPotentialPart r.1 r.2)
      (g := fun q : (ℕ × ℕ) × ℕ ↦ (cofinalData sel baseIdx q.1.1, q.2))
      K.applyPotentialPart_recursiveIn
      (((cofinalData_computableIn (baseIdx := baseIdx) hsel).comp
        (ComputableIn.fst.comp ComputableIn.fst)).pair ComputableIn.snd)
  have h₃ : RecursiveIn O fun r : ((ℕ × ℕ) × ℕ) × ℕ ↦ Z.rankStageMap (r.1.1.1 + 1) r.2 :=
    RecursiveIn.comp (O := O) (α := ((ℕ × ℕ) × ℕ) × ℕ) (β := ℕ × ℕ) (σ := ℕ)
      (f := fun p : ℕ × ℕ ↦ Z.rankStageMap p.1 p.2)
      (g := fun r : ((ℕ × ℕ) × ℕ) × ℕ ↦ (r.1.1.1 + 1, r.2))
      Z.rankStageMap_recursiveIn
      (((Primrec.succ.to_comp.computableIn (O := O)).comp
        (ComputableIn.fst.comp (ComputableIn.fst.comp ComputableIn.fst))).pair ComputableIn.snd)
  exact RecursiveIn.bind h₁ (RecursiveIn.bind h₂ h₃.to₂).to₂

/-! ### The cover -/

/-- **The cofinal embedding of `K` into its own ω-limit**, packaged for the generated-image
constructor: semantic embeddings, program, uniformity, exact domain, and the bridge. -/
noncomputable def toLimitEmbedding : UniformEmbeddingIntoIn O K (limitStructure Z cert) where
  embedding := omegaEmbedding Z cert
  map := omegaMap Z
  map_uniform := omegaMap_uniform Z
  map_dom := omegaMap_dom Z cert
  map_apply_mem := omegaEmbedding_mem_omegaMap Z cert

@[simp] theorem toLimitEmbedding_map : (toLimitEmbedding Z cert).map = omegaMap Z :=
  rfl

/-- **The backward cover `K → 𝕂_𝒟`.** An application of the generated-image constructor: its index
map is `encode` of the generator-image tuple, and every structure law comes from the constructor. -/
noncomputable def backwardCover :
    RepresentationCoverIn O K (limitStructure Z cert).canonicalAge :=
  (toLimitEmbedding Z cert).toCanonicalAgeCover (Set.Subset.refl O)

@[simp] theorem backwardCover_indexMap (i : ℕ) :
    (backwardCover Z cert).indexMap i = encode ((toLimitEmbedding Z cert).toSelected.imageTuple i) :=
  rfl

/-- **The backward cover is generator-compatible** — the constructor's theorem, with no new
coordinate argument. This is the half of Theorem 2.10(⇐)'s compatibility that
`allTupleFor_encode` supplies. -/
theorem backwardCover_generatorCompatible :
    (backwardCover Z cert).GeneratorCompatible :=
  (toLimitEmbedding Z cert).toCanonicalAgeCover_generatorCompatible (Set.Subset.refl O)

end PartialAgeIn

end FirstOrder.Language
