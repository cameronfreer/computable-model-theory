/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.CeStructureLimitPresentation

/-!
# The ω-limit adapter: rank-recoding the Lemma 2.9 limit

Lemma 2.9 delivers a Level-1 presentation whose carrier is the set of **accepted codes** — a c.e.
subset of ℕ, not ℕ. A consumer that wants an all-ℕ `ComputableStructureIn` must upgrade through
`upgradeOmega`, and `upgradeOmega` carries the **rank-recoded** structure `rankStr`, not the
extensional limit structure. So the Lemma 2.9 stage embeddings do not transport definitionally:
they land in the wrong carrier. Re-deriving them past the recoding is the whole content here.

Two boundaries are worth stating up front.

**The certificate buys the carrier, not the embedding.** `rankEmbedding` and
`omegaStageEmbedding` need no `InfinitudeCertificate` — the rank structure lives on all of ℕ
regardless, and the stage maps rank whatever they produce. The certificate is required for exactly
one of the four laws, coverage: without it the rank domain is a proper initial segment and the
stage images miss the naturals past it. Keeping the certificate off the embeddings makes that
dependency visible instead of ambient.

**No commuting squares are re-proved.** `rankEmbedding` is `rankIso` composed with the subtype
inclusion `domainInclusion`; the function and relation laws come from `rankIso.toEquiv`, which is
where `rankStr_funMap_mem_rankOf` and `rankStr_relMap_iff` already did that work. The single new
bridging fact is `rankEmbedding_apply_mem`, tying the noncomputable bundled map back to the partial
`rankOf` — and every other law below is a two-line consequence of it plus the corresponding
Lemma 2.9 law.

No record is bundled. The four laws are stated separately until a consumer shows which shape it
wants; the CHMM Theorem 2.10 covers are the first candidates, and they are not written yet.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

namespace CeStructureChainIn

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable {D : CeStructureChainIn O L}

namespace LimitIn

variable (Z : D.LimitIn)

/-! ### The ω structure

Three explicit steps, no coercions: the Lemma 2.9 presentation, its certified upgrade to shape
`omega`, and the conversion of that upgrade to an all-ℕ computable structure. -/

/-- The Level-2 upgrade of the limit: shape `omega`, carrying the rank recoding. -/
noncomputable def omegaPresentation (cert : Z.presentation.InfinitudeCertificate) :
    ComputableInitialSegmentPresentationIn O L :=
  Z.presentation.upgradeOmega cert

@[simp]
theorem omegaPresentation_shape (cert : Z.presentation.InfinitudeCertificate) :
    (Z.omegaPresentation cert).shape = .omega :=
  rfl

@[simp]
theorem omegaPresentation_domain (cert : Z.presentation.InfinitudeCertificate) :
    (Z.omegaPresentation cert).domain = Set.univ :=
  rfl

/-- **The ω-limit as an all-ℕ computable structure.** -/
noncomputable def omegaStructure (cert : Z.presentation.InfinitudeCertificate) :
    ComputableStructureIn O L :=
  (Z.omegaPresentation cert).toComputableStructure rfl

/-- **Adapter law 4: the target interpretation is exactly the ω structure's.** Definitional, and
that is the point — every statement below names `Z.presentation.rankStr` as the ambient structure
on ℕ, and this says that naming is not a weaker claim than naming `(Z.omegaStructure cert).inst`.
Note the right-hand side does not mention `cert`: the interpretation is certificate-independent,
and the certificate contributes only the domain shape. -/
theorem omegaStructure_inst (cert : Z.presentation.InfinitudeCertificate) :
    (Z.omegaStructure cert).inst = Z.presentation.rankStr :=
  rfl

/-! ### The effective rank-lifted stage map

`Z.stageMap` lands in the accepted codes; `rankOf` ranks them. Written in exactly the bind
association its recursiveness proof follows. -/

/-- The stage map into the ω carrier: run the Lemma 2.9 stage map, then rank its value. Partial,
with no exact-domain claim — inherited from `stageMap`, which makes none either. -/
noncomputable def rankStageMap (i : ℕ) : ℕ →. ℕ :=
  fun x ↦ (Z.stageMap i x).bind Z.presentation.rankOf

/-- Uniformly partial recursive in the stage, from the Lemma 2.9 field and `rankOf`. -/
theorem rankStageMap_recursiveIn :
    RecursiveIn O fun p : ℕ × ℕ ↦ Z.rankStageMap p.1 p.2 :=
  RecursiveIn.bind Z.stageMap_recursiveIn
    ((Z.presentation.rankOf_recursiveIn.comp ComputableIn.snd).to₂)

/-! ### The semantic stage embedding -/

/-- The rank recoding as an embedding into the ambient ℕ: `rankIso`, followed by the inclusion of
the rank presentation's carrier subtype. The structure laws are `rankIso`'s. -/
noncomputable def rankEmbedding :
    @Language.Embedding L Z.presentation.domain ℕ _ Z.presentation.rankStr :=
  letI : L.Structure ℕ := Z.presentation.rankStr
  Z.presentation.rankPresentation.domainInclusion.comp
    Z.presentation.rankIso.toEquiv.toEmbedding

/-- **The bridging fact.** The bundled embedding's value is a value of the partial `rankOf` — the
one statement relating the semantic recoding to the effective one, and the source of every law
below. -/
theorem rankEmbedding_apply_mem (c : Z.presentation.domain) :
    Z.rankEmbedding c ∈ Z.presentation.rankOf (c : ℕ) :=
  Z.presentation.rankIso.toSubtypeFun_mem c

/-- **The rank-lifted stage embedding**: the Lemma 2.9 stage embedding, recoded. -/
noncomputable def omegaStageEmbedding (i : ℕ) :
    @Language.Embedding L (D.stageAt i).domain ℕ _ Z.presentation.rankStr :=
  letI : L.Structure ℕ := Z.presentation.rankStr
  Z.rankEmbedding.comp (Z.stageEmbedding i)

@[simp]
theorem omegaStageEmbedding_apply (i : ℕ) (x : (D.stageAt i).domain) :
    Z.omegaStageEmbedding i x = Z.rankEmbedding (Z.stageEmbedding i x) :=
  rfl

/-! ### The adapter laws -/

/-- **Adapter law 1: the two sides agree.** The bundled recoded embedding's value is a value of the
uniformly partial recursive `rankStageMap` — the ω-side counterpart of
`LimitIn.stageEmbedding_apply_mem`, and what keeps the package from carrying a semantic map and a
program with nothing relating them. -/
theorem omegaStageEmbedding_apply_mem (i : ℕ) (x : (D.stageAt i).domain) :
    Z.omegaStageEmbedding i x ∈ Z.rankStageMap i x.1 :=
  Part.mem_bind_iff.2
    ⟨_, Z.stageEmbedding_apply_mem i x, Z.rankEmbedding_apply_mem _⟩

/-- **Adapter law 2: coherence at every realized chain step.** Stated for whichever step value a
consumer already has, matching `LimitIn.stageEmbedding_step` — recoding is a function, so the
Lemma 2.9 equality transports directly. -/
theorem omegaStageEmbedding_step {i x y : ℕ} (hx : x ∈ (D.stageAt i).domain)
    (hy : y ∈ D.toDomainChain.step i x) :
    ∃ hy' : y ∈ (D.stageAt (i + 1)).domain,
      Z.omegaStageEmbedding i ⟨x, hx⟩ = Z.omegaStageEmbedding (i + 1) ⟨y, hy'⟩ := by
  obtain ⟨hy', heq⟩ := Z.stageEmbedding_step hx hy
  exact ⟨hy', by simp only [omegaStageEmbedding_apply, heq]⟩

/-- **Adapter law 3: coverage of all of ω.** Every natural number — not merely every carrier
element — is a stage image. This is the one law that consumes the certificate: it supplies the rank
position, `rankEnum` names an element of the limit carrier at that position, generic Lemma 2.9
coverage puts that element in a stage, and `rankOf_rankEnum` identifies the recoded value as the
rank we started from. -/
theorem exists_omegaStageEmbedding_eq (cert : Z.presentation.InfinitudeCertificate) (n : ℕ) :
    ∃ (i x : ℕ) (hx : x ∈ (D.stageAt i).domain), Z.omegaStageEmbedding i ⟨x, hx⟩ = n := by
  have hdom : (Z.presentation.rankEnum n).Dom :=
    (Z.presentation.rankEnum_dom_iff n).2 (cert.rankIdx_dom n)
  have hcmem : (Z.presentation.rankEnum n).get hdom ∈ Z.presentation.rankEnum n :=
    Part.get_mem _
  have hcdom : (Z.presentation.rankEnum n).get hdom ∈ Z.presentation.domain :=
    Z.presentation.mem_domain_of_mem_rankEnum hcmem
  obtain ⟨i, x, hx, heq⟩ := Z.coverage ⟨_, hcdom⟩
  refine ⟨i, x, hx, ?_⟩
  have hval : Z.omegaStageEmbedding i ⟨x, hx⟩ = Z.rankEmbedding ⟨_, hcdom⟩ := by
    simp only [omegaStageEmbedding_apply, heq]
  rw [hval]
  exact Part.mem_unique (Z.rankEmbedding_apply_mem ⟨_, hcdom⟩)
    (Z.presentation.rankOf_rankEnum hcmem)

end LimitIn

end CeStructureChainIn

end FirstOrder.Language
