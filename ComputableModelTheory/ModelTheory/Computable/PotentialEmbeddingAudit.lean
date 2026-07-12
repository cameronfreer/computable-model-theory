/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PotentialEmbedding
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for potential embeddings

Named acceptance tests for potential embedding data, actualness, and realization,
checked by `#assert_standard_axioms`. Outside the root import spine; CI checks it
explicitly with

```
lake env lean ComputableModelTheory/ModelTheory/Computable/PotentialEmbeddingAudit.lean
```
-/

open Encodable FirstOrder Language Language.BoundedFormula

section

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable {K : ComputableAgeIn O L} {F : PotentialEmbeddingData}

/-- Potential embedding data is primitively codable independently of any age. -/
@[reducible]
def test_potentialEmbeddingData_primcodable : Primcodable PotentialEmbeddingData :=
  inferInstance

/-- The target view is independent of the well-formedness proof. -/
theorem test_targetView_irrel (h h' : F.WellFormed K) :
    F.targetView h = F.targetView h' :=
  F.targetView_irrel h h'

/-- Malformed data is never actual. -/
theorem test_not_isEmbedding_of_not_wellFormed (hn : ¬F.WellFormed K) :
    ¬F.IsEmbedding K :=
  PotentialEmbeddingData.not_isEmbedding_of_not_wellFormed hn

/-- The identity potential embedding is actual. -/
theorem test_id_isEmbedding (i : ℕ) : (PotentialEmbeddingData.id K i).IsEmbedding K :=
  PotentialEmbeddingData.id_isEmbedding K i

/-- The realized embedding carries generators to range entries. -/
theorem test_toEmbedding_apply_gens (h : F.WellFormed K)
    (hAE : @AtomicEquivalent L ℕ ℕ (K.structureAt F.domIdx)
      (K.structureAt F.codIdx) _ (K.gens F.domIdx).view (F.targetView h))
    (i : Fin (K.gens F.domIdx).length) :
    PotentialEmbeddingData.toEmbedding h hAE ((K.gens F.domIdx).view i) =
      F.targetView h i :=
  PotentialEmbeddingData.toEmbedding_apply_gens h hAE i

/-- Actualness is the existence of an embedding extending the tuple assignment. -/
theorem test_isEmbedding_iff :
    F.IsEmbedding K ↔
      ∃ (h : F.WellFormed K)
        (g : @Language.Embedding L ↥(K.presentationAt F.domIdx).toBundled
          ↥(K.presentationAt F.codIdx).toBundled
          (K.structureAt F.domIdx) (K.structureAt F.codIdx)),
        ∀ i, g ((K.gens F.domIdx).view i) = F.targetView h i :=
  PotentialEmbeddingData.isEmbedding_iff_exists_embedding_extending_tuple

end

section ConcretePotentialEmbedding

variable (O : Set (ℕ →. ℕ))

/-- The identity potential embedding of the successor age is actual. -/
theorem test_succ_id_isEmbedding :
    (PotentialEmbeddingData.id (succAge O) 0).IsEmbedding (succAge O) :=
  PotentialEmbeddingData.id_isEmbedding (succAge O) 0

/-- An empty range tuple against a one-generator object is malformed, hence not
actual. -/
theorem test_succ_malformed_not_isEmbedding :
    ¬(⟨0, 0, []⟩ : PotentialEmbeddingData).IsEmbedding (succAge O) :=
  PotentialEmbeddingData.not_isEmbedding_of_not_wellFormed (by
    simp [PotentialEmbeddingData.WellFormed, succAge])

end ConcretePotentialEmbedding

#assert_standard_axioms test_potentialEmbeddingData_primcodable
#assert_standard_axioms test_targetView_irrel
#assert_standard_axioms test_not_isEmbedding_of_not_wellFormed
#assert_standard_axioms test_id_isEmbedding
#assert_standard_axioms test_toEmbedding_apply_gens
#assert_standard_axioms test_isEmbedding_iff
#assert_standard_axioms test_succ_id_isEmbedding
#assert_standard_axioms test_succ_malformed_not_isEmbedding
