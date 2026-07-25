/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PartialAgeSemantics
import ComputableModelTheory.ModelTheory.Computable.IndexedProperties

/-!
# The realized-embedding bridge for all-ℕ witness adapters

Every all-ℕ adapter — hereditary, joint embedding, amalgamation — has to cross the same gap
in both directions: between *actualness of potential embedding data* (`IsEmbedding`, a coded
atomic-equivalence statement about `ℕ`) and *a member embedding carrying the domain
generators coordinatewise onto the range tuple* (what the partial-family interfaces state).

Both crossings already exist for individual pieces:
`PotentialEmbeddingData.toEmbedding` realizes actual data as a genuine embedding of the
stored structures with `toEmbedding_apply_gens` for the coordinates, and
`isEmbedding_of_embedding_extending_tuple` runs the converse. This file packages the pair at
arbitrary data, so no adapter rebuilds a closure equivalence or re-derives a carrier change:
the carrier change is `ComputableAgeIn.embeddingToPartial`/`embeddingOfPartial`, conjugating
through the bundled carrier whose structure instance is registered.

`Fin.cast` is confined here. `WellFormed` measures the range tuple against the generators
while the partial-family interfaces measure the generators against the range tuple, so the
two conventions are each other's `symm` (`wellFormed_iff_gens_length`) and no adapter below
mentions a cast.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable {K : ComputableAgeIn O L}

namespace PotentialEmbeddingData

/-- The two length conventions are each other's `symm`. -/
theorem wellFormed_iff_gens_length {F : PotentialEmbeddingData} :
    F.WellFormed K ↔ (K.gens F.domIdx).length = F.rangeTuple.length :=
  eq_comm

/-- **Actual data yields a member embedding on coordinates.** From actualness of potential
embedding data to an embedding of the corresponding all-ℕ members' carriers carrying the
domain's recorded generators coordinatewise onto the range tuple. -/
theorem exists_memberEmbedding_of_isEmbedding {F : PotentialEmbeddingData}
    (hF : F.IsEmbedding K) :
    ∃ hlen : (K.toPartialAge.gens F.domIdx).length = F.rangeTuple.length,
      ∃ G : (K.toPartialAge.memberAt F.domIdx).domain ↪[L]
          (K.toPartialAge.memberAt F.codIdx).domain,
        ∀ k : Fin (K.toPartialAge.gens F.domIdx).length,
          ((G ⟨(K.toPartialAge.gens F.domIdx).get k, K.toPartialAge.gens_mem_domainAt k⟩ :
            (K.toPartialAge.memberAt F.codIdx).domain) : ℕ) =
            F.rangeTuple.get (Fin.cast hlen k) := by
  obtain ⟨h, hAE⟩ := hF
  refine ⟨wellFormed_iff_gens_length.1 h, K.embeddingToPartial (F.toEmbedding h hAE),
    fun k ↦ ?_⟩
  rw [K.embeddingToPartial_coe]
  exact F.toEmbedding_apply_gens h hAE k

/-- The indexed form: the domain and codomain indices are supplied as parameters together
with equations identifying them. Adapters know their indices from well-shapedness rather than
by projection, and substituting *there* would rewrite the types of hypotheses other
hypotheses depend on; doing it here, where the indices are genuine variables, keeps `subst`
available and keeps every adapter free of transport. -/
theorem exists_memberEmbedding_of_isEmbedding' {F : PotentialEmbeddingData} {d a : ℕ}
    (hF : F.IsEmbedding K) (hd : F.domIdx = d) (ha : F.codIdx = a) :
    ∃ hlen : (K.toPartialAge.gens d).length = F.rangeTuple.length,
      ∃ G : (K.toPartialAge.memberAt d).domain ↪[L] (K.toPartialAge.memberAt a).domain,
        ∀ k : Fin (K.toPartialAge.gens d).length,
          ((G ⟨(K.toPartialAge.gens d).get k, K.toPartialAge.gens_mem_domainAt k⟩ :
            (K.toPartialAge.memberAt a).domain) : ℕ) =
            F.rangeTuple.get (Fin.cast hlen k) := by
  subst hd
  subst ha
  exact exists_memberEmbedding_of_isEmbedding hF

/-- **A member embedding on coordinates yields actual data.** The converse crossing. -/
theorem isEmbedding_of_memberEmbedding {F : PotentialEmbeddingData}
    (hlen : (K.toPartialAge.gens F.domIdx).length = F.rangeTuple.length)
    (G : (K.toPartialAge.memberAt F.domIdx).domain ↪[L]
      (K.toPartialAge.memberAt F.codIdx).domain)
    (hG : ∀ k : Fin (K.toPartialAge.gens F.domIdx).length,
      ((G ⟨(K.toPartialAge.gens F.domIdx).get k, K.toPartialAge.gens_mem_domainAt k⟩ :
        (K.toPartialAge.memberAt F.codIdx).domain) : ℕ) =
        F.rangeTuple.get (Fin.cast hlen k)) :
    F.IsEmbedding K :=
  F.isEmbedding_of_embedding_extending_tuple (wellFormed_iff_gens_length.2 hlen)
    (K.embeddingOfPartial G) fun k ↦ hG k

end PotentialEmbeddingData

end FirstOrder.Language
