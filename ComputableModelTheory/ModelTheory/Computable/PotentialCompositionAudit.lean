/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PotentialComposition
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for composition of potential embedding data

Named acceptance tests for `compData`, its transport helpers, and `paperComp`, checked by
`#assert_standard_axioms`. Outside the root import spine; CI checks it explicitly with

```
lake env lean ComputableModelTheory/ModelTheory/Computable/PotentialCompositionAudit.lean
```

Coverage: composition's oracle-computability; the projection identities; minimal
well-formedness; actualness of a composite; the functoriality of transport and the
realized-embedding composition; the identity and associativity laws; and both branches of the
paper totalization.
-/

open Encodable FirstOrder Language

section

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-- Composition is oracle-computable, uniformly in both potential embeddings. -/
theorem test_compData_computableIn (K : ComputableAgeIn O L) :
    ComputableIn O fun p : PotentialEmbeddingData × PotentialEmbeddingData ↦
      K.compData p.1 p.2 :=
  K.compData_computableIn

/-- The projections of a composite: `F`'s domain, `G`'s codomain, `F`'s transported tuple. -/
theorem test_compData_proj (K : ComputableAgeIn O L) (G F : PotentialEmbeddingData) :
    (K.compData G F).domIdx = F.domIdx ∧ (K.compData G F).codIdx = G.codIdx ∧
      (K.compData G F).rangeTuple = F.rangeTuple.map (K.transportValue G) :=
  ⟨rfl, rfl, rfl⟩

/-- Composition preserves well-formedness, needing only `F`'s. -/
theorem test_compData_wellFormed (K : ComputableAgeIn O L) {G F : PotentialEmbeddingData}
    (hF : F.WellFormed K) : (K.compData G F).WellFormed K :=
  K.compData_wellFormed hF

/-- Composition of actual data with matching middle index is actual. -/
theorem test_compData_isEmbedding (K : ComputableAgeIn O L) {G F : PotentialEmbeddingData}
    (hFG : F.codIdx = G.domIdx) (hF : F.IsEmbedding K) (hG : G.IsEmbedding K) :
    (K.compData G F).IsEmbedding K :=
  K.compData_isEmbedding hFG hF hG

/-- Functoriality of transport along a composite: composing transports. -/
theorem test_transportValue_compData (K : ComputableAgeIn O L) {G H : PotentialEmbeddingData}
    (hGH : G.codIdx = H.domIdx) (hG : G.IsEmbedding K) (hH : H.IsEmbedding K) (x : ℕ) :
    K.transportValue (K.compData H G) x = K.transportValue H (K.transportValue G x) :=
  K.transportValue_compData hGH hG hH x

/-- The realized embedding of a composite is the composition of realized embeddings. -/
theorem test_toEmbedding_compData (K : ComputableAgeIn O L) {F G : PotentialEmbeddingData}
    (hFG : F.codIdx = G.domIdx) (hFwf : F.WellFormed K)
    (hFAE : @AtomicEquivalent L ℕ ℕ (K.structureAt F.domIdx) (K.structureAt F.codIdx) _
      (K.gens F.domIdx).view (F.targetView hFwf)) (hGwf : G.WellFormed K)
    (hGAE : @AtomicEquivalent L ℕ ℕ (K.structureAt G.domIdx) (K.structureAt G.codIdx) _
      (K.gens G.domIdx).view (G.targetView hGwf)) (hcwf : (K.compData G F).WellFormed K)
    (hcAE : @AtomicEquivalent L ℕ ℕ (K.structureAt (K.compData G F).domIdx)
      (K.structureAt (K.compData G F).codIdx) _ (K.gens (K.compData G F).domIdx).view
      ((K.compData G F).targetView hcwf)) (x : ℕ) :
    (K.compData G F).toEmbedding hcwf hcAE x
      = G.toEmbedding hGwf hGAE (F.toEmbedding hFwf hFAE x) :=
  K.toEmbedding_compData hFG hFwf hFAE hGwf hGAE hcwf hcAE x

/-- Left and right identity laws. -/
theorem test_compData_id (K : ComputableAgeIn O L) (F : PotentialEmbeddingData)
    {G : PotentialEmbeddingData} (hG : G.IsEmbedding K) :
    K.compData (PotentialEmbeddingData.id K F.codIdx) F = F ∧
      K.compData G (PotentialEmbeddingData.id K G.domIdx) = G :=
  ⟨K.compData_id_left F, K.compData_id_right hG⟩

/-- Associativity of composition as code data. -/
theorem test_compData_assoc (K : ComputableAgeIn O L) {F G H : PotentialEmbeddingData}
    (hGH : G.codIdx = H.domIdx) (hG : G.IsEmbedding K) (hH : H.IsEmbedding K) :
    K.compData H (K.compData G F) = K.compData (K.compData H G) F :=
  K.compData_assoc hGH hG hH

/-- The paper totalization uses the composite on actual `G`. -/
theorem test_paperComp_actual (K : ComputableAgeIn O L) (G F : PotentialEmbeddingData)
    (hG : G.IsEmbedding K) : K.paperComp G F = K.compData G F := by
  unfold ComputableAgeIn.paperComp
  exact if_pos hG

/-- The paper totalization falls back off actual `G`. -/
theorem test_paperComp_fallback (K : ComputableAgeIn O L) (G F : PotentialEmbeddingData)
    (hG : ¬ G.IsEmbedding K) : K.paperComp G F = ⟨F.domIdx, G.codIdx, G.rangeTuple⟩ := by
  unfold ComputableAgeIn.paperComp
  exact if_neg hG

end

#assert_standard_axioms test_compData_computableIn
#assert_standard_axioms test_compData_proj
#assert_standard_axioms test_compData_wellFormed
#assert_standard_axioms test_compData_isEmbedding
#assert_standard_axioms test_transportValue_compData
#assert_standard_axioms test_toEmbedding_compData
#assert_standard_axioms test_compData_id
#assert_standard_axioms test_compData_assoc
#assert_standard_axioms test_paperComp_actual
#assert_standard_axioms test_paperComp_fallback
