/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.RunChain
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: the chain of the constructed run

**The recorded connecting maps are the assembly's input.** `test_step_endpoints_actual` reads the
run invariant back as the three fields of `EmbeddingChainData`; `test_base_member` says the chain
starts at the requested member.

**The assembled chain.** `test_stage_domain` (carriers are the members' carriers),
`test_chain_step` (steps are the recorded maps, applied), `test_uniform_evaluators`.

**Transport identification, after assembly.** `test_recorded_transport_is_fold` identifies the
finite transport computed off the run's prefix with the assembly's fold; `test_transport` then
reads the chain's carrier transport as the application of the recorded transport data. This is the
theorem the contract deferred until the chain existed.

**Effectivity.** `test_effective` records that the member-index function and the connecting maps are
computable at any oracle reading the family and running the selector — `O ⊆ E` appears only there
and in the chain's own oracle.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable {K : PartialAgeIn O L} (W : PartialCAPWitness E K) (i : ℕ)

theorem test_step_endpoints_actual (n : ℕ) :
    (PartialAgeIn.runStep K W i n).domIdx = PartialAgeIn.memberIdx K W i n ∧
      (PartialAgeIn.runStep K W i n).codIdx = PartialAgeIn.memberIdx K W i (n + 1) ∧
        K.PartialIsEmbedding (PartialAgeIn.runStep K W i n) :=
  ⟨PartialAgeIn.runStep_domIdx n, PartialAgeIn.runStep_codIdx n, PartialAgeIn.runStep_isEmbedding n⟩

theorem test_base_member : PartialAgeIn.memberIdx K W i 0 = i := PartialAgeIn.memberIdx_zero

theorem test_stage_domain (hOE : O ⊆ E) (h0 : (K.domainAt i).Nonempty) (n : ℕ) :
    ((PartialAgeIn.runChain K W i hOE h0).stageAt n).domain =
      K.domainAt (PartialAgeIn.memberIdx K W i n) :=
  PartialAgeIn.runChain_stage_domain K W i hOE h0 n

theorem test_chain_step (hOE : O ⊆ E) (h0 : (K.domainAt i).Nonempty) (n x : ℕ) :
    (PartialAgeIn.runChain K W i hOE h0).step n x =
      K.applyPotentialPart (PartialAgeIn.runStep K W i n) x :=
  PartialAgeIn.runChain_step K W i hOE h0 n x

theorem test_uniform_evaluators (hOE : O ⊆ E) (h0 : (K.domainAt i).Nonempty) :
    (PartialAgeIn.runChain K W i hOE h0).UniformEvaluatorsIn :=
  PartialAgeIn.runChain_uniformEvaluators K W i hOE h0

/-- **The recorded transport is the fold.** -/
theorem test_recorded_transport_is_fold (r k : ℕ) :
    K.transportPart (PartialAgeIn.run K W i (r + k)).stages r (r + k) =
      (PartialAgeIn.runChainData K W i).foldData r k :=
  PartialAgeIn.transportPart_eq_foldData r k

/-- **Transport identification on the run.** -/
theorem test_transport (hOE : O ⊆ E) (h0 : (K.domainAt i).Nonempty) {r s : ℕ} (hrs : r ≤ s)
    {δ : PotentialEmbeddingData} (hδ : δ ∈ K.transportPart (PartialAgeIn.run K W i s).stages r s)
    {x y : ℕ} (hx : x ∈ K.domainAt (PartialAgeIn.memberIdx K W i r)) :
    y ∈ (PartialAgeIn.runChain K W i hOE h0).transportTo r s x ↔ y ∈ K.applyPotentialPart δ x :=
  PartialAgeIn.mem_transportTo_iff_transportPart hOE h0 hrs hδ hx

theorem test_effective (hOE : O ⊆ E) :
    ComputableIn E (PartialAgeIn.memberIdx K W i) ∧ ComputableIn E (PartialAgeIn.runStep K W i) :=
  ⟨PartialAgeIn.memberIdx_computableIn K W i hOE, PartialAgeIn.runStep_computableIn K W i hOE⟩

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.test_step_endpoints_actual
#assert_standard_axioms FirstOrder.Language.test_base_member
#assert_standard_axioms FirstOrder.Language.test_stage_domain
#assert_standard_axioms FirstOrder.Language.test_chain_step
#assert_standard_axioms FirstOrder.Language.test_uniform_evaluators
#assert_standard_axioms FirstOrder.Language.test_recorded_transport_is_fold
#assert_standard_axioms FirstOrder.Language.test_transport
#assert_standard_axioms FirstOrder.Language.test_effective
