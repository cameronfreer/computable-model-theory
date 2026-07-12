/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.EmbeddingInformation
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for uniform nonembedding witnesses and embedding information

Named acceptance tests for the uniform r.e. failure of actualness and the semantic
embedding information, checked by `#assert_standard_axioms`. Outside the root import
spine; CI checks it explicitly with

```
lake env lean ComputableModelTheory/ModelTheory/Computable/EmbeddingInformationAudit.lean
```
-/

open Encodable FirstOrder Language

section

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable (K : ComputableAgeIn O L)

/-- Well-formedness is computable uniformly in the data. -/
theorem test_wellFormed_computable :
    ComputablePredIn O fun F : PotentialEmbeddingData ↦ F.WellFormed K :=
  K.wellFormed_computablePredIn

/-- Atomic disagreement is computable uniformly in the data and witness. -/
theorem test_atomicDisagreement_computable :
    ComputablePredIn O fun p : PotentialEmbeddingData × AtomicData L ℕ ↦
      K.AtomicDisagreement p.1 p.2 :=
  K.atomicDisagreement_computablePredIn

/-- The tagged search characterizes non-actualness. -/
theorem test_candidate_iff (F : PotentialEmbeddingData) :
    (∃ n, K.nonEmbeddingCandidate F n) ↔ ¬F.IsEmbedding K :=
  K.exists_nonEmbeddingCandidate_iff F

/-- A disagreement witness supplies a candidate, independently of coding. -/
theorem test_candidate_of_disagreement {F : PotentialEmbeddingData}
    {d : AtomicData L ℕ} (hd : K.AtomicDisagreement F d) :
    ∃ n, K.nonEmbeddingCandidate F n :=
  K.exists_nonEmbeddingCandidate_of_atomicDisagreement hd

/-- Non-actualness is uniformly r.e. in the oracle. -/
theorem test_not_isEmbedding_rePredIn :
    REPredIn O fun F : PotentialEmbeddingData ↦ ¬F.IsEmbedding K :=
  K.not_isEmbedding_rePredIn

/-- The complement of embedding information is r.e. in the oracle. -/
theorem test_embeddingInformation_compl_rePredIn :
    REPredIn O fun F : PotentialEmbeddingData ↦ F ∈ (EmbeddingInformation K)ᶜ :=
  embeddingInformation_compl_rePredIn K

end

section ConcreteWitness

variable (O : Set (ℕ →. ℕ))

/-- The identity data of the successor age lies in embedding information. -/
theorem test_succ_id_mem_embeddingInformation :
    PotentialEmbeddingData.id (succAge O) 0 ∈ EmbeddingInformation (succAge O) :=
  PotentialEmbeddingData.id_isEmbedding (succAge O) 0

/-- Malformed data is witnessed by candidate `0`. -/
theorem test_succ_malformed_candidate :
    (succAge O).nonEmbeddingCandidate (⟨0, 0, []⟩ : PotentialEmbeddingData) 0 := by
  show ¬(⟨0, 0, []⟩ : PotentialEmbeddingData).WellFormed (succAge O)
  simp [PotentialEmbeddingData.WellFormed, succAge]

end ConcreteWitness

#assert_standard_axioms test_wellFormed_computable
#assert_standard_axioms test_atomicDisagreement_computable
#assert_standard_axioms test_candidate_iff
#assert_standard_axioms test_candidate_of_disagreement
#assert_standard_axioms test_not_isEmbedding_rePredIn
#assert_standard_axioms test_embeddingInformation_compl_rePredIn
#assert_standard_axioms test_succ_id_mem_embeddingInformation
#assert_standard_axioms test_succ_malformed_candidate
