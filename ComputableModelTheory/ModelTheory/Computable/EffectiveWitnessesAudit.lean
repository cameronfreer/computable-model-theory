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

/-- Gate: the derived AP witness shares the selector and computability proof
unchanged. -/
theorem test_capWitness_toAP_shared (W : CAPWitnessIn E K) :
    W.toAPWitnessIn.select = W.select ∧
      W.toAPWitnessIn.computable = W.computable ∧ W.toAPWitnessIn.sound = W.sound :=
  ⟨rfl, rfl, rfl⟩

/-- Gate: the unconditional clauses hold on every raw span code. -/
theorem test_capWitness_unconditional (W : CAPWitnessIn E K) (S : PotentialSpanData) :
    (W.select S).WellShapedFor S ∧ (W.select S).leftToApex.IsEmbedding K ∧
      (W.select S).rightToApex.WellFormed K :=
  ⟨W.shape S, W.leftToApex_isEmbedding S, W.rightToApex_wellFormed S⟩

/-- Gate: conditional soundness assumes exactly span actualness, and a CAP witness
yields `IndexedAP`. -/
theorem test_capWitness_sound (W : CAPWitnessIn E K) (S : PotentialSpanData)
    (hS : S.IsActual K) : (W.select S).IsAmalgamationOf K S ∧ K.IndexedAP :=
  ⟨W.sound S hS, W.indexedAP⟩

end

section ConcreteCAP

variable {E : Set (ℕ →. ℕ)} (O : Set (ℕ →. ℕ))

/-- A malformed span code over the successor age: the left leg's empty range tuple has
the wrong length against the one-generator object. -/
def malformedSpan : PotentialSpanData :=
  ⟨⟨0, 0, []⟩, PotentialEmbeddingData.id (succAge O) 0⟩

/-- The malformed span is not actual — conditional soundness gives nothing on it. -/
theorem malformedSpan_not_isActual : ¬(malformedSpan O).IsActual (succAge O) :=
  fun h ↦ PotentialEmbeddingData.not_isEmbedding_of_not_wellFormed
    (by simp [malformedSpan, PotentialEmbeddingData.WellFormed, succAge])
    h.isEmbedding_left

/-- Gate (malformed input): the unconditional clauses still deliver on a span code with
a wrong tuple length. -/
theorem test_capWitness_on_malformed (W : CAPWitnessIn E (succAge O)) :
    (W.select (malformedSpan O)).WellShapedFor (malformedSpan O) ∧
      (W.select (malformedSpan O)).leftToApex.IsEmbedding (succAge O) ∧
      (W.select (malformedSpan O)).rightToApex.WellFormed (succAge O) :=
  ⟨W.shape _, W.leftToApex_isEmbedding _, W.rightToApex_wellFormed _⟩


/-- A well-formed but nonembedding code over the two-generator successor age: `0 ↦ 1`,
`1 ↦ 3` has the right tuple length but breaks the successor atom `S(x₀) = x₁`. -/
theorem wfNonembedding :
    (⟨0, 0, [1, 3]⟩ : PotentialEmbeddingData).WellFormed (succAge2 O) ∧
      ¬(⟨0, 0, [1, 3]⟩ : PotentialEmbeddingData).IsEmbedding (succAge2 O) := by
  refine ⟨rfl, ?_⟩
  rintro ⟨hwf, hAE⟩
  have h20 : (0 : ℕ) < ((succAge2 O).gens 0).length := by
    show (0 : ℕ) < 2
    omega
  have h21 : (1 : ℕ) < ((succAge2 O).gens 0).length := by
    show (1 : ℕ) < 2
    omega
  have h := hAE.1 (Term.func SuccFunctions.succ ![Term.var ⟨0, h20⟩])
    (Term.var ⟨1, h21⟩)
  have hcontra : (1 : ℕ) + 1 = 3 := h.1 rfl
  omega

/-- The nonembedding span: both legs the well-formed nonembedding code. Well-shaped,
not actual. -/
def wfNonembeddingSpan : PotentialSpanData :=
  ⟨⟨0, 0, [1, 3]⟩, ⟨0, 0, [1, 3]⟩⟩

theorem wfNonembeddingSpan_not_isActual :
    (wfNonembeddingSpan).WellShaped ∧ ¬(wfNonembeddingSpan).IsActual (succAge2 O) :=
  ⟨rfl, fun h ↦ (wfNonembedding O).2 h.isEmbedding_left⟩

/-- Gate (invalid-map input): the unconditional clauses still deliver on a well-formed
span whose maps are not embeddings — the case the totalization convention exists for. -/
theorem test_capWitness_on_wfNonembedding (W : CAPWitnessIn E (succAge2 O)) :
    (W.select wfNonembeddingSpan).WellShapedFor wfNonembeddingSpan ∧
      (W.select wfNonembeddingSpan).leftToApex.IsEmbedding (succAge2 O) ∧
      (W.select wfNonembeddingSpan).rightToApex.WellFormed (succAge2 O) :=
  ⟨W.shape _, W.leftToApex_isEmbedding _, W.rightToApex_wellFormed _⟩

end ConcreteCAP

#assert_standard_axioms test_capWitness_toAP_shared
#assert_standard_axioms test_capWitness_unconditional
#assert_standard_axioms test_capWitness_sound
#assert_standard_axioms malformedSpan_not_isActual
#assert_standard_axioms test_capWitness_on_malformed
#assert_standard_axioms wfNonembedding
#assert_standard_axioms wfNonembeddingSpan_not_isActual
#assert_standard_axioms test_capWitness_on_wfNonembedding

#assert_standard_axioms test_hpWitness_computable
#assert_standard_axioms test_jepWitness_computable
#assert_standard_axioms test_apWitness_computable
#assert_standard_axioms test_hpWitness_sound
#assert_standard_axioms test_hpWitness_indexedHP
#assert_standard_axioms test_jepWitness_indexedJEP
#assert_standard_axioms test_apWitness_indexedAP
