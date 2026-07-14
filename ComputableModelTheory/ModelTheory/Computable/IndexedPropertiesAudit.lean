/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.IndexedProperties
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for indexed HP/JEP/AP

Named acceptance tests for joint embedding data and the indexed classical properties,
checked by `#assert_standard_axioms`. Outside the root import spine; CI checks it via
`scripts/run-audit-modules.sh`.

Coverage: the `Primcodable` instance, computable projections, and pair factory for
`JointEmbeddingData`; the free diagonal joint embedding; the free one-sided amalgamation;
and the shapes of `IndexedHP` / `IndexedJEP` / `IndexedAP` as consumed by downstream
witness extraction.
-/

open Encodable FirstOrder Language

section

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable {K : ComputableAgeIn O L}

/-- Joint embedding data is primitively codable independently of any age. -/
@[reducible]
def test_jointEmbeddingData_primcodable : Primcodable JointEmbeddingData :=
  inferInstance

/-- The joint-embedding projections and pair factory are computable in the oracle. -/
theorem test_jointEmbeddingData_computable (O : Set (ℕ →. ℕ)) :
    ComputableIn O JointEmbeddingData.leftInto ∧
      ComputableIn O JointEmbeddingData.rightInto ∧
      ComputableIn O JointEmbeddingData.ofPair :=
  ⟨JointEmbeddingData.leftInto_computable, JointEmbeddingData.rightInto_computable,
    JointEmbeddingData.ofPair_computableIn⟩

/-- The diagonal joint embedding is free (non-vacuity). -/
theorem test_exists_isJointEmbeddingOf_diag (i : ℕ) :
    ∃ J : JointEmbeddingData, J.IsJointEmbeddingOf K i i :=
  JointEmbeddingData.exists_isJointEmbeddingOf_diag K i

/-- One-sided amalgamation is free (non-vacuity). -/
theorem test_isAmalgamationOf_id_span {G : PotentialEmbeddingData}
    (hG : G.IsEmbedding K) :
    (⟨G, PotentialEmbeddingData.id K G.codIdx⟩ :
        AmalgamationDiagramData).IsAmalgamationOf K
      ⟨PotentialEmbeddingData.id K G.domIdx, G⟩ :=
  K.isAmalgamationOf_id_span hG

/-- `IndexedHP` produces, for any tuple in any object, an actual map with that range —
the exact shape `HPWitnessIn` soundness will refine. -/
theorem test_indexedHP_shape (h : K.IndexedHP) (i : ℕ) (a : Tuple ℕ) :
    ∃ j : ℕ, (⟨j, i, a⟩ : PotentialEmbeddingData).IsEmbedding K :=
  h i a

/-- `IndexedJEP` produces joint embedding data for any pair of indices. -/
theorem test_indexedJEP_shape (h : K.IndexedJEP) (i j : ℕ) :
    ∃ J : JointEmbeddingData, J.IsJointEmbeddingOf K i j :=
  h i j

/-- `IndexedAP` consumes span actualness as a hypothesis and produces an amalgamation
diagram — the exact shape `APWitnessIn` soundness will refine. -/
theorem test_indexedAP_shape (h : K.IndexedAP) (S : PotentialSpanData)
    (hS : S.IsActual K) : ∃ D : AmalgamationDiagramData, D.IsAmalgamationOf K S :=
  h S hS

end

section ConcreteIndexed

variable (O : Set (ℕ →. ℕ))

/-- The diagonal joint embedding of the successor age at index 0. -/
theorem test_succ_diag_jointEmbedding :
    ∃ J : JointEmbeddingData, J.IsJointEmbeddingOf (succAge O) 0 0 :=
  JointEmbeddingData.exists_isJointEmbeddingOf_diag (succAge O) 0

end ConcreteIndexed

#assert_standard_axioms test_jointEmbeddingData_primcodable
#assert_standard_axioms test_jointEmbeddingData_computable
#assert_standard_axioms test_exists_isJointEmbeddingOf_diag
#assert_standard_axioms test_isAmalgamationOf_id_span
#assert_standard_axioms test_indexedHP_shape
#assert_standard_axioms test_indexedJEP_shape
#assert_standard_axioms test_indexedAP_shape
#assert_standard_axioms test_succ_diag_jointEmbedding
