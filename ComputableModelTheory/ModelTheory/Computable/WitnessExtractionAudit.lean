/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.WitnessExtraction
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for witness extraction

Named acceptance tests for the abstract search lemma and the EI-route extraction
theorems, checked by `#assert_standard_axioms`. Outside the root import spine; CI
checks it via `scripts/run-audit-modules.sh`.

Coverage: the abstract selector-from-decidable-candidate lemma; candidate decidability
for each witness kind; and the three extractions — hereditary and joint-embedding from
EI decidability alone (their candidates touch no `O`-computable presentation data), and
the CAP extraction carrying the oracle lifting `O ⊆ E` explicitly, with the derived AP
extraction through `toAPWitnessIn`.
-/

open Encodable FirstOrder Language

section

variable {α β : Type*} [Primcodable α] [Primcodable β] [Inhabited β]
variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable {K : ComputableAgeIn O L}

/-- The abstract search scheme: decidable candidate plus existence yields a computable
selector with its soundness. -/
theorem test_exists_computableIn_selector {cand : α → β → Prop}
    (hdec : ComputablePredIn E fun p : α × β ↦ cand p.1 p.2)
    (hex : ∀ a, ∃ b, cand a b) :
    ∃ select : α → β, ComputableIn E select ∧ ∀ a, cand a (select a) :=
  exists_computableIn_selector hdec hex

/-- Candidate decidability: assembled actualness (EI alone), joint embedding (EI
alone), and composed-data equality (EI plus the oracle lifting). -/
theorem test_candidate_decidability (hOE : O ⊆ E)
    (hEI : EmbeddingInformationComputableIn E K) :
    ComputablePredIn E (fun q : (ℕ × Tuple ℕ) × ℕ ↦
      (⟨q.2, q.1.1, q.1.2⟩ : PotentialEmbeddingData).IsEmbedding K) ∧
    ComputablePredIn E (fun q : (ℕ × ℕ) × JointEmbeddingData ↦
      q.2.IsJointEmbeddingOf K q.1.1 q.1.2) ∧
    ComputablePredIn E (fun q : PotentialSpanData × AmalgamationDiagramData ↦
      K.compData q.2.leftToApex q.1.left = K.compData q.2.rightToApex q.1.right) :=
  ⟨isEmbedding_assembled_computablePredIn hEI,
    isJointEmbeddingOf_computablePredIn hEI,
    compData_eq_computablePredIn hOE⟩

/-- EI-route extraction: a hereditary witness from `IndexedHP` and EI decidability. -/
theorem test_exists_hpWitnessIn (h : K.IndexedHP)
    (hEI : EmbeddingInformationComputableIn E K) : Nonempty (HPWitnessIn E K) :=
  h.exists_hpWitnessIn hEI

/-- EI-route extraction: a joint-embedding witness from `IndexedJEP` and EI
decidability. -/
theorem test_exists_jepWitnessIn (h : K.IndexedJEP)
    (hEI : EmbeddingInformationComputableIn E K) : Nonempty (JEPWitnessIn E K) :=
  h.exists_jepWitnessIn hEI

/-- EI-route extraction: a CAP witness from `IndexedAP`, EI decidability, **and the
oracle lifting `O ⊆ E`** — the candidate reads `K.gens` and computes `K.compData`. -/
theorem test_exists_capWitnessIn (h : K.IndexedAP) (hOE : O ⊆ E)
    (hEI : EmbeddingInformationComputableIn E K) : Nonempty (CAPWitnessIn E K) :=
  h.exists_capWitnessIn hOE hEI

/-- The derived AP-witness extraction, through `toAPWitnessIn`. -/
theorem test_exists_apWitnessIn (h : K.IndexedAP) (hOE : O ⊆ E)
    (hEI : EmbeddingInformationComputableIn E K) : Nonempty (APWitnessIn E K) :=
  h.exists_apWitnessIn hOE hEI

end

#assert_standard_axioms test_exists_computableIn_selector
#assert_standard_axioms test_candidate_decidability
#assert_standard_axioms test_exists_hpWitnessIn
#assert_standard_axioms test_exists_jepWitnessIn
#assert_standard_axioms test_exists_capWitnessIn
#assert_standard_axioms test_exists_apWitnessIn
