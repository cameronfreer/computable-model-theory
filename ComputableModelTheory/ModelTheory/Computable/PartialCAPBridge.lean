/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PartialCAP
import ComputableModelTheory.ModelTheory.Computable.PartialWitnessBridge

/-!
# The partial predicates on a full carrier

Where the amalgamation predicates of `PartialMemberEmbedding` land when the family is the
all-ℕ embedding of a `ComputableAgeIn`. Every apparent mismatch between `PartialCAPIn` and
`CAPWitnessIn` dissolves here:

* carrier validity is **automatic** (`carrierValid_toPartialAge`), so a partial amalgamation
  selector is required to halt on *every* input — which is what will let `computableIn_get`
  recover a total selector;
* `PartialWellFormed` collapses to `WellFormed`, since codomain membership in `univ` is free
  and only the length equation survives;
* `PartialIsEmbedding` matches `IsEmbedding`, by the two crossings of
  `PartialWitnessBridge`;
* `PartialSpanActual` matches `IsActual`, componentwise.

The off-carrier half of the partial contract is invisible from here — on a full carrier there
is no off-carrier input — so the four-row audit of the partial selector's domain behavior stays
separate from this adapter, which cannot exercise it.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable {K : ComputableAgeIn O L}

namespace PartialAgeIn

/-! ### Carrier validity is free -/

/-- On a full carrier every range tuple is valid. -/
theorem carrierValid_toPartialAge (K : ComputableAgeIn O L) (F : PotentialEmbeddingData) :
    K.toPartialAge.CarrierValid F :=
  fun x _ ↦ K.mem_toPartialAge_memberAt_domain F.codIdx x

/-- Hence every span is carrier-valid: an all-ℕ amalgamation selector is required to halt
everywhere. -/
theorem carrierValidSpan_toPartialAge (K : ComputableAgeIn O L) (S : PotentialSpanData) :
    K.toPartialAge.CarrierValidSpan S :=
  ⟨carrierValid_toPartialAge K S.left, carrierValid_toPartialAge K S.right⟩

/-! ### The predicates collapse to their all-ℕ forms -/

/-- Well-formedness collapses to the length equation: codomain membership is free. -/
theorem partialWellFormed_iff_wellFormed {F : PotentialEmbeddingData} :
    K.toPartialAge.PartialWellFormed F ↔ F.WellFormed K :=
  ⟨fun h ↦ PotentialEmbeddingData.wellFormed_iff_gens_length.2 h.length,
    fun h ↦ ⟨carrierValid_toPartialAge K F,
      PotentialEmbeddingData.wellFormed_iff_gens_length.1 h⟩⟩

/-- Realizability matches actualness, by the two crossings of the shared bridge. -/
theorem partialIsEmbedding_iff_isEmbedding {F : PotentialEmbeddingData} :
    K.toPartialAge.PartialIsEmbedding F ↔ F.IsEmbedding K := by
  constructor
  · rintro ⟨f, hlen, hcoord⟩
    exact PotentialEmbeddingData.isEmbedding_of_memberEmbedding hlen f hcoord
  · intro hF
    obtain ⟨hlen, G, hG⟩ :=
      PotentialEmbeddingData.exists_memberEmbedding_of_isEmbedding hF
    exact ⟨G, hlen, hG⟩

/-- Span actualness matches, componentwise. -/
theorem partialSpanActual_iff_isActual {S : PotentialSpanData} :
    K.toPartialAge.PartialSpanActual S ↔ S.IsActual K :=
  and_congr_right fun _ ↦
    and_congr partialIsEmbedding_iff_isEmbedding partialIsEmbedding_iff_isEmbedding

/-! ### The canonical realizer

The realized embedding of actual data, crossed into the member carriers, realizes that data —
at **named** indices, so it can be fed to `partialCommutes_iff_of_realizers` without transport.
This is the witness the commutativity bridge will instantiate. -/

theorem partialRealizesAt_embeddingToPartial {F : PotentialEmbeddingData} {d a : ℕ}
    (hF : F.IsEmbedding K) (hd : F.domIdx = d) (ha : F.codIdx = a) :
    ∃ f : (K.toPartialAge.memberAt d).domain ↪[L] (K.toPartialAge.memberAt a).domain,
      K.toPartialAge.PartialRealizesAt F d a f := by
  obtain ⟨hlen, G, hG⟩ :=
    PotentialEmbeddingData.exists_memberEmbedding_of_isEmbedding' hF hd ha
  exact ⟨G, hd, ha, hlen, hG⟩

/-! ### Semantic commutativity is coded commutativity

The chain is

```
PartialCommutes S D
  ↔ crossed realizer composites are equal        (partialCommutes_iff_of_realizers)
  ↔ raw embeddings agree pointwise on ℕ          (embeddingToPartial_comp_eq_iff_pointwise)
  ↔ D.IsAmalgamationOf K S                       (isAmalgamationOf_iff_toEmbedding_comm)
```

`PartialCommutes` uses a **single** index per middle object, which is the mathematically correct
shape for a square. The coded representation instead carries a separate index on each side of
every middle object, related only by `WellShapedFor` — equations between *projections*, so no
`subst` is available at the use site. The mismatch is therefore representational, and it is
repaired here rather than in the semantic API: `reindexPresentationEmbedding` transports the
**raw presentation** embedding along an index equation *before* conjugation, in a context where
the indices are genuine variables. `PartialCommutes` stays transport-free.

The helper is private on purpose. It is glue for this coded boundary; promote it only when a
second consumer (witness transport) actually needs it. -/

/-- Transport a presentation embedding along equations naming its two indices. Stated so the
equations can be eliminated by `subst`, which is what the use site cannot do. -/
private noncomputable def reindexPE (K : ComputableAgeIn O L) {c e d a : ℕ}
    (hc : c = d) (he : e = a)
    (f : (K.presentationAt c).toBundled ↪[L] (K.presentationAt e).toBundled) :
    (K.presentationAt d).toBundled ↪[L] (K.presentationAt a).toBundled := by
  subst hc
  subst he
  exact f

/-- The transport does not move any value: its underlying map on `ℕ` is the original's. Used
explicitly; the transport is never unfolded or `simp`ed away. -/
private theorem reindexPE_apply (K : ComputableAgeIn O L) {c e d a : ℕ}
    (hc : c = d) (he : e = a)
    (f : (K.presentationAt c).toBundled ↪[L] (K.presentationAt e).toBundled) (x : ℕ) :
    reindexPE K hc he f x = f x := by
  subst hc
  subst he
  rfl

/-- The reindexed realized embedding, conjugated into the member carriers, realizes its data at
the named indices. Proved inside the named-variable helper by `subst`, so the CAP use site never
transports this fact. -/
private theorem partialRealizesAt_reindexPE (K : ComputableAgeIn O L)
    {F : PotentialEmbeddingData} {d a : ℕ} (hwf : F.WellFormed K)
    (hAE : @AtomicEquivalent L ℕ ℕ (K.structureAt F.domIdx) (K.structureAt F.codIdx) _
      (K.gens F.domIdx).view (F.targetView hwf))
    (hd : F.domIdx = d) (ha : F.codIdx = a) :
    K.toPartialAge.PartialRealizesAt F d a
      (K.embeddingToPartial (reindexPE K hd ha (F.toEmbedding hwf hAE))) := by
  subst hd
  subst ha
  refine ⟨rfl, rfl, PotentialEmbeddingData.wellFormed_iff_gens_length.1 hwf, fun k ↦ ?_⟩
  rw [K.embeddingToPartial_coe]
  exact F.toEmbedding_apply_gens hwf hAE k

/-- The first two links: semantic commutativity is pointwise agreement on `ℕ` of any raw
embeddings whose conjugations realize the four legs. -/
theorem partialCommutes_iff_pointwise {S : PotentialSpanData}
    {D : AmalgamationDiagramData} {d m₁ m₂ a : ℕ}
    {fl : (K.presentationAt d).toBundled ↪[L] (K.presentationAt m₁).toBundled}
    {gl : (K.presentationAt m₁).toBundled ↪[L] (K.presentationAt a).toBundled}
    {fr : (K.presentationAt d).toBundled ↪[L] (K.presentationAt m₂).toBundled}
    {gr : (K.presentationAt m₂).toBundled ↪[L] (K.presentationAt a).toBundled}
    (hfl : K.toPartialAge.PartialRealizesAt S.left d m₁ (K.embeddingToPartial fl))
    (hfr : K.toPartialAge.PartialRealizesAt S.right d m₂ (K.embeddingToPartial fr))
    (hgl : K.toPartialAge.PartialRealizesAt D.leftToApex m₁ a (K.embeddingToPartial gl))
    (hgr : K.toPartialAge.PartialRealizesAt D.rightToApex m₂ a (K.embeddingToPartial gr)) :
    K.toPartialAge.PartialCommutes S D ↔ ∀ x : ℕ, gl (fl x) = gr (fr x) :=
  (partialCommutes_iff_of_realizers hfl hfr hgl hgr).trans
    (K.embeddingToPartial_comp_eq_iff_pointwise fl gl fr gr)

/-- **Semantic commutativity matches the coded amalgamation predicate.** On an actual span with
actual, well-shaped output maps, the square of `PartialCommutes` commutes exactly when the
diagram amalgamates in the coded sense. -/
theorem partialCommutes_iff_isAmalgamationOf {S : PotentialSpanData}
    {D : AmalgamationDiagramData} (hSd : S.WellShaped) (hshape : D.WellShapedFor S)
    (hSlwf : S.left.WellFormed K)
    (hSlAE : @AtomicEquivalent L ℕ ℕ (K.structureAt S.left.domIdx)
      (K.structureAt S.left.codIdx) _ (K.gens S.left.domIdx).view (S.left.targetView hSlwf))
    (hSrwf : S.right.WellFormed K)
    (hSrAE : @AtomicEquivalent L ℕ ℕ (K.structureAt S.right.domIdx)
      (K.structureAt S.right.codIdx) _ (K.gens S.right.domIdx).view
      (S.right.targetView hSrwf))
    (hlwf : D.leftToApex.WellFormed K)
    (hlAE : @AtomicEquivalent L ℕ ℕ (K.structureAt D.leftToApex.domIdx)
      (K.structureAt D.leftToApex.codIdx) _ (K.gens D.leftToApex.domIdx).view
      (D.leftToApex.targetView hlwf))
    (hrwf : D.rightToApex.WellFormed K)
    (hrAE : @AtomicEquivalent L ℕ ℕ (K.structureAt D.rightToApex.domIdx)
      (K.structureAt D.rightToApex.codIdx) _ (K.gens D.rightToApex.domIdx).view
      (D.rightToApex.targetView hrwf)) :
    K.toPartialAge.PartialCommutes S D ↔ D.IsAmalgamationOf K S := by
  refine Iff.trans ?_ (D.isAmalgamationOf_iff_toEmbedding_comm hSd hshape hSlwf hSlAE hSrwf
    hSrAE hlwf hlAE hrwf hrAE).symm
  refine (partialCommutes_iff_pointwise
    (partialRealizesAt_reindexPE K hSlwf hSlAE rfl rfl)
    (partialRealizesAt_reindexPE K hSrwf hSrAE (Eq.symm hSd) rfl)
    (partialRealizesAt_reindexPE K hlwf hlAE hshape.1 rfl)
    (partialRealizesAt_reindexPE K hrwf hrAE hshape.2.1
      (Eq.symm hshape.2.2))).trans ?_
  refine forall_congr' fun x ↦ ?_
  rw [reindexPE_apply, reindexPE_apply, reindexPE_apply, reindexPE_apply]
  exact Iff.rfl

end PartialAgeIn

end FirstOrder.Language
