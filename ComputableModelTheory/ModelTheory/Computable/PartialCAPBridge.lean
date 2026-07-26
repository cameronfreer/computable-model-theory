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

end PartialAgeIn

end FirstOrder.Language
