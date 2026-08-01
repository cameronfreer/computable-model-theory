/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PartialFiniteChecker
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for the Observation 2.7 finite checker

Named acceptance tests for the executable checker and the decision procedure it supports,
checked by `#assert_standard_axioms`. Outside the root import spine; CI checks it explicitly
with

```
lake env lean ComputableModelTheory/ModelTheory/Computable/PartialFiniteCheckerAudit.lean
```
-/

open FirstOrder Language

section

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage] [EffectivelyFiniteLanguage L]
variable {B : PartialAgeIn O L} (C : ExactFiniteCarriers B)

/-- The checker is a total `Bool` of arbitrary data and code — no validity hypothesis. -/
theorem test_finiteMapCheck_total (F : PotentialEmbeddingData) (f : List ℕ) :
    C.finiteMapCheck F f = true ∨ C.finiteMapCheck F f = false := by
  cases h : C.finiteMapCheck F f
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- Semantic gate: the checker decides realization, on arbitrary input. -/
theorem test_finiteMapCheck_eq_true_iff (F : PotentialEmbeddingData) (f : List ℕ) :
    C.finiteMapCheck F f = true ↔ C.FiniteMapRealizes F f :=
  C.finiteMapCheck_eq_true_iff F f

/-- Bridge gate: the Boolean value is `Part` membership, with `Part.get` never exposed. -/
theorem test_finiteMapCheck_eq_true_iff_mem (F : PotentialEmbeddingData) (f : List ℕ) :
    C.finiteMapCheck F f = true ↔ true ∈ C.finiteMapCheckPart F f :=
  C.finiteMapCheck_eq_true_iff_mem F f

/-- Finite-search gate: bounded to the enumerated candidates. -/
theorem test_exists_mem_finiteMaps (F : PotentialEmbeddingData) :
    (∃ f ∈ C.finiteMaps F.domIdx F.codIdx, C.finiteMapCheck F f = true) ↔
      B.PartialIsEmbedding F :=
  C.exists_mem_finiteMaps_finiteMapCheck_iff F

/-- Computability gate for the checker. -/
theorem test_finiteMapCheck_computableIn :
    ComputableIn O fun q : PotentialEmbeddingData × List ℕ ↦ C.finiteMapCheck q.1 q.2 :=
  C.finiteMapCheck_computableIn

end

#assert_standard_axioms test_finiteMapCheck_total
#assert_standard_axioms test_finiteMapCheck_eq_true_iff
#assert_standard_axioms test_finiteMapCheck_eq_true_iff_mem
#assert_standard_axioms test_exists_mem_finiteMaps
#assert_standard_axioms test_finiteMapCheck_computableIn
