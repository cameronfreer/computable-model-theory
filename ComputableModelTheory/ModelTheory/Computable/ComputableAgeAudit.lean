/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.ComputableAge
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for uniform computable ages

Named acceptance tests for the uniform age representation and its represented
classical age, checked by `#assert_standard_axioms`. Outside the root import spine; CI
checks it explicitly with

```
lake env lean ComputableModelTheory/ModelTheory/Computable/ComputableAgeAudit.lean
```
-/

open Encodable FirstOrder Language Language.BoundedFormula

section

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable (K : ComputableAgeIn O L)

/-- Generator computation is uniform over varying indices. -/
theorem test_gens_uniform : ComputableIn O K.gens :=
  K.gens_computableIn

/-- Function interpretation is uniform over varying indices. -/
theorem test_funMap_uniform :
    ComputableIn O fun p : ℕ × FunctionApplicationData L ℕ ↦
      @FunctionApplicationData.funMap L ℕ (K.structureAt p.1) p.2 :=
  K.funMap_computableIn

/-- Relation interpretation is uniform over varying indices. -/
theorem test_relMap_uniform :
    ComputablePredIn O fun p : ℕ × RelationApplicationData L ℕ ↦
      @RelationApplicationData.relMap L ℕ (K.structureAt p.1) p.2 :=
  K.relMap_computablePredIn

/-- The presentation at a fixed index satisfies the generated-presentation
contracts. -/
theorem test_presentationAt_contracts (i : ℕ) (k : ℕ) :
    ComputablePredIn O ((K.presentationAt i).completeAtomicDiagram k) ∧
      ComputablePredIn O ((K.presentationAt i).completeQFDiagram k) :=
  ⟨(K.presentationAt i).completeAtomicDiagram_computablePredIn k,
    (K.presentationAt i).completeQFDiagram_computablePredIn k⟩

/-- Two distinct indices coexist without structure-instance ambiguity. -/
theorem test_two_indices_coexist (i j k : ℕ) :
    ComputablePredIn O ((K.presentationAt i).posAtomicDiagram k) ∧
      ComputablePredIn O ((K.presentationAt j).negQFDiagram k) :=
  ⟨(K.presentationAt i).posAtomicDiagram_computablePredIn k,
    (K.presentationAt j).negQFDiagram_computablePredIn k⟩

/-- Every enumerated object lies in the represented class. -/
theorem test_obj_mem_classSet (i : ℕ) :
    (K.presentationAt i).toBundled ∈ K.classSet :=
  K.obj_mem_classSet i

/-- The represented class is isomorphism-invariant. -/
theorem test_classSet_equiv_invariant {A B : CategoryTheory.Bundled L.Structure}
    (hA : A ∈ K.classSet) (e : A ≃[L] B) : B ∈ K.classSet :=
  K.classSet_equiv_invariant hA e

/-- Every member of the represented class is finitely generated. -/
theorem test_classSet_finitelyGenerated {A : CategoryTheory.Bundled L.Structure}
    (hA : A ∈ K.classSet) : Structure.FG L A :=
  K.classSet_finitelyGenerated hA

/-- The membership characterization. -/
theorem test_contains_iff (A : CategoryTheory.Bundled L.Structure) :
    K.Contains A ↔ ∃ i, Nonempty ((K.presentationAt i).toBundled ≃[L] A) :=
  K.contains_iff A

end

section ConcreteAge

/-- The constant successor family is a computable age, and its generators are as
declared. -/
theorem test_succAge_gens (O : Set (ℕ →. ℕ)) (i : ℕ) : (succAge O).gens i = [0] :=
  rfl

/-- The successor object lies in its represented class. -/
theorem test_succAge_mem (O : Set (ℕ →. ℕ)) :
    ((succAge O).presentationAt 5).toBundled ∈ (succAge O).classSet :=
  (succAge O).obj_mem_classSet 5

end ConcreteAge

#assert_standard_axioms test_gens_uniform
#assert_standard_axioms test_funMap_uniform
#assert_standard_axioms test_relMap_uniform
#assert_standard_axioms test_presentationAt_contracts
#assert_standard_axioms test_two_indices_coexist
#assert_standard_axioms test_obj_mem_classSet
#assert_standard_axioms test_classSet_equiv_invariant
#assert_standard_axioms test_classSet_finitelyGenerated
#assert_standard_axioms test_contains_iff
#assert_standard_axioms test_succAge_gens
#assert_standard_axioms test_succAge_mem
