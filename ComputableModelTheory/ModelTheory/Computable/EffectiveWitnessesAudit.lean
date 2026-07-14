/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.EffectiveWitnesses
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for the effective witness interfaces

Named acceptance tests for the HP/JEP/AP witness structures, checked by
`#assert_standard_axioms`. Outside the root import spine; CI checks it via
`scripts/run-audit-modules.sh`.

Coverage: each structure elaborates with its computability field consumable at its
stated type, and each witness yields the corresponding indexed property. No witness is
constructed — the stop boundary defers extraction.
-/

open Encodable FirstOrder Language

section

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable {K : ComputableAgeIn O L}

/-- The HP selector's computability field has its stated type. -/
theorem test_hpWitness_computable (W : HPWitnessIn E K) : ComputableIn E W.select :=
  W.computable

/-- The JEP selector's computability field has its stated type. -/
theorem test_jepWitness_computable (W : JEPWitnessIn E K) : ComputableIn E W.select :=
  W.computable

/-- The AP selector's computability field has its stated type. -/
theorem test_apWitness_computable (W : APWitnessIn E K) : ComputableIn E W.select :=
  W.computable

/-- The HP soundness law has the shape item 5 specifies. -/
theorem test_hpWitness_sound (W : HPWitnessIn E K) (i : ℕ) (a : Tuple ℕ) :
    (⟨W.select (i, a), i, a⟩ : PotentialEmbeddingData).IsEmbedding K :=
  W.sound i a

/-- An HP witness yields `IndexedHP`. -/
theorem test_hpWitness_indexedHP (W : HPWitnessIn E K) : K.IndexedHP :=
  W.indexedHP

/-- A JEP witness yields `IndexedJEP`. -/
theorem test_jepWitness_indexedJEP (W : JEPWitnessIn E K) : K.IndexedJEP :=
  W.indexedJEP

/-- An AP witness yields `IndexedAP`, with span actualness consumed as a hypothesis. -/
theorem test_apWitness_indexedAP (W : APWitnessIn E K) : K.IndexedAP :=
  W.indexedAP

end

#assert_standard_axioms test_hpWitness_computable
#assert_standard_axioms test_jepWitness_computable
#assert_standard_axioms test_apWitness_computable
#assert_standard_axioms test_hpWitness_sound
#assert_standard_axioms test_hpWitness_indexedHP
#assert_standard_axioms test_jepWitness_indexedJEP
#assert_standard_axioms test_apWitness_indexedAP
