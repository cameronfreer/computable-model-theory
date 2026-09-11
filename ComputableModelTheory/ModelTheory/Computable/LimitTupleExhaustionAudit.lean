/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.LimitTupleExhaustion
import ComputableModelTheory.ModelTheory.Computable.CollapsingCandidate
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: finite-tuple exhaustion

**Three forms, gated separately.** `test_level_one` (the limit presentation), `test_omega` (the
all-ℕ ω structure, under the infinitude certificate), `test_semantic` (the semantic limit). The ω
form is the one Theorem 3.9's homogeneity half consumes; the certificate is the only hypothesis it
adds, and it is the one coverage of ω requires.

**Two tuples at once.** `test_two_tuples` places two tuples in a single stage, which is how the
opening of the homogeneity argument uses the statement (`d⃗` and `c⃗` together).

**A concrete limit.** On the identity chain over member `0` of the three-width family, the Level-1
limit exists by Lemma 2.9, and `test_identity_limit_pair` places any pair of its elements in one
stage.
-/

open FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage] {D : CeStructureChainIn O L}

theorem test_level_one (Z : D.LimitIn) {n : ℕ} (v : Fin n → Z.presentation.domain) :
    ∃ (i : ℕ) (w : Fin n → ℕ) (hw : ∀ k, w k ∈ (D.stageAt i).domain),
      ∀ k, Z.stageEmbedding i ⟨w k, hw k⟩ = v k :=
  Z.exists_stage_tuple v

theorem test_omega (Z : D.LimitIn) (cert : Z.presentation.InfinitudeCertificate) {n : ℕ}
    (v : Fin n → ℕ) :
    ∃ (i : ℕ) (w : Fin n → ℕ) (hw : ∀ k, w k ∈ (D.stageAt i).domain),
      ∀ k, Z.omegaStageEmbedding i ⟨w k, hw k⟩ = v k :=
  Z.exists_omegaStage_tuple cert v

theorem test_semantic {n : ℕ} (v : Fin n → D.Limit) :
    ∃ (i : ℕ) (w : Fin n → ℕ) (hw : ∀ k, w k ∈ (D.stageAt i).domain),
      ∀ k, D.stageIntoLimit i (w k) (hw k) = v k :=
  D.exists_stageIntoLimit_tuple v

/-- **Two tuples in one stage**, through the list form. -/
theorem test_two_tuples (Z : D.LimitIn) (cert : Z.presentation.InfinitudeCertificate)
    (l₁ l₂ : List ℕ) :
    ∃ i : ℕ, ∀ m, m ∈ l₁ ∨ m ∈ l₂ → ∃ (x : ℕ) (hx : x ∈ (D.stageAt i).domain),
      Z.omegaStageEmbedding i ⟨x, hx⟩ = m := by
  obtain ⟨i, hi⟩ := Z.exists_omegaStage_list cert (l₁ ++ l₂)
  exact ⟨i, fun m hm ↦ hi m (List.mem_append.2 hm)⟩

/-! ### A concrete limit -/

section Fixture

variable (O : Set (ℕ →. ℕ)) (hOE : O ⊆ O)

/-- The Level-1 limit of the identity chain, by Lemma 2.9. -/
noncomputable def identityLimit :
    ((identityChain O).toChain (identityChain_nonempty O) hOE (ComputableIn.const 0)
      (ComputableIn.const _)).LimitIn :=
  ((identityChain O).toChain (identityChain_nonempty O) hOE (ComputableIn.const 0)
    (ComputableIn.const _)).toLimit ((identityChain O).toChain_uniformEvaluators _ hOE _ _)

/-- **Any pair of limit elements lies in one stage.** -/
theorem test_identity_limit_pair (c₁ c₂ : (identityLimit O hOE).presentation.domain) :
    ∃ (i x₁ x₂ : ℕ) (hx₁ : x₁ ∈ (((identityChain O).toChain (identityChain_nonempty O) hOE
        (ComputableIn.const 0) (ComputableIn.const _)).stageAt i).domain)
      (hx₂ : x₂ ∈ (((identityChain O).toChain (identityChain_nonempty O) hOE
        (ComputableIn.const 0) (ComputableIn.const _)).stageAt i).domain),
      (identityLimit O hOE).stageEmbedding i ⟨x₁, hx₁⟩ = c₁ ∧
        (identityLimit O hOE).stageEmbedding i ⟨x₂, hx₂⟩ = c₂ := by
  obtain ⟨i, w, hw, heq⟩ := (identityLimit O hOE).exists_stage_tuple ![c₁, c₂]
  exact ⟨i, w 0, w 1, hw 0, hw 1, heq 0, heq 1⟩

end Fixture

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.test_level_one
#assert_standard_axioms FirstOrder.Language.test_omega
#assert_standard_axioms FirstOrder.Language.test_semantic
#assert_standard_axioms FirstOrder.Language.test_two_tuples
#assert_standard_axioms FirstOrder.Language.test_identity_limit_pair
