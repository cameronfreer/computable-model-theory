/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.ChainAssembly
import ComputableModelTheory.ModelTheory.Computable.CollapsingCandidate
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: the generic chain assembly

**The assembly asks only for a nonempty base.** `test_nonempty_propagates` is the propagation along
the injective steps; `test_stage_domain` says totalizing did not move any carrier.

**Steps are the realizers.** `test_step_is_realizer` is the one realizer lemma the four laws are
read through; `test_chain_step` says the assembled chain's step is exactly the partial application.

**Transport identification is a theorem about the finished chain.** `test_fold_actual` and
`test_fold_halts` are the fold's own properties; `test_transport_identification` is the statement
that the chain's carrier transport is the application of any fold value.

**A concrete identity chain.** On the three-width family, the constant chain on member `0` with the
identity data at every step assembles, and its transport from `0` to any stage is the identity on
the member (`test_identity_chain_transport`), read through the identification with a fold whose
values are all realized by the identity.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

section General

variable {K : PartialAgeIn O L} (C : K.EmbeddingChainData) (h0 : (K.domainAt (C.d 0)).Nonempty)
  (hOE : O ⊆ E) (hd : ComputableIn E C.d) (hstep : ComputableIn E C.step)

include h0 in
theorem test_nonempty_propagates (n : ℕ) : (K.domainAt (C.d n)).Nonempty :=
  C.domainAt_nonempty h0 n

theorem test_stage_domain (n : ℕ) :
    ((C.toChain h0 hOE hd hstep).stageAt n).domain = K.domainAt (C.d n) :=
  C.toChain_stage_domain h0 hOE hd hstep n

theorem test_step_is_realizer {n : ℕ}
    {f : (K.memberAt (C.step n).domIdx).domain ↪[L] (K.memberAt (C.step n).codIdx).domain}
    (hf : K.PartialRealizes (C.step n) f) {x y : ℕ}
    (hx : x ∈ (K.memberAt (C.step n).domIdx).domain) :
    y ∈ C.chainStep n x ↔ y = ((f ⟨x, hx⟩ : (K.memberAt (C.step n).codIdx).domain) : ℕ) :=
  C.mem_chainStep_iff hf hx

theorem test_chain_step (n x : ℕ) :
    (C.toChain h0 hOE hd hstep).step n x = K.applyPotentialPart (C.step n) x := rfl

theorem test_uniform_evaluators : (C.toChain h0 hOE hd hstep).UniformEvaluatorsIn :=
  C.toChain_uniformEvaluators h0 hOE hd hstep

theorem test_fold_actual (r k : ℕ) {δ : PotentialEmbeddingData} (h : δ ∈ C.foldData r k) :
    δ.domIdx = C.d r ∧ δ.codIdx = C.d (r + k) ∧ K.PartialIsEmbedding δ :=
  C.foldData_partialIsEmbedding r k h

theorem test_fold_halts (r k : ℕ) : (C.foldData r k).Dom := C.foldData_dom r k

/-- **Transport identification.** -/
theorem test_transport_identification (r k : ℕ) {δ : PotentialEmbeddingData}
    (h : δ ∈ C.foldData r k) {x y : ℕ} (hx : x ∈ K.domainAt (C.d r)) :
    y ∈ (C.toChain h0 hOE hd hstep).transportTo r (r + k) x ↔ y ∈ K.applyPotentialPart δ x :=
  C.mem_transportTo_iff_applyPotentialPart h0 hOE hd hstep r k h hx

end General

/-! ### A concrete identity chain -/

section Fixture

variable (O : Set (ℕ →. ℕ))

/-- Every fold value of the identity chain is realized by the identity: it sends any point to
itself. -/
theorem test_identity_fold (k : ℕ) {δ : PotentialEmbeddingData}
    (h : δ ∈ (identityChain O).foldData 0 k) (x : ℕ) :
    x ∈ (threeWidthFamily O).applyPotentialPart δ x := by
  induction k generalizing δ with
  | zero =>
    rw [PartialAgeIn.EmbeddingChainData.foldData_zero, Part.mem_some_iff] at h
    subst h
    exact ((threeWidthFamily O).mem_applyPotentialPart_idData_iff
      (by simp [threeWidthFamily])).2 rfl
  | succ k ih =>
    rw [PartialAgeIn.EmbeddingChainData.foldData_succ, Part.mem_bind_iff] at h
    obtain ⟨δ₀, h₀, hδ⟩ := h
    obtain ⟨hdom, hcod, hemb⟩ := (identityChain O).foldData_partialIsEmbedding 0 k h₀
    exact PartialAgeIn.mem_applyPotentialPart_of_mem_compPart (K := threeWidthFamily O)
      (by rw [hcod]; rfl) hemb ((threeWidthFamily O).idData_partialIsEmbedding 0) hδ
      (by rw [hdom]; simp [threeWidthFamily]) (ih h₀)
      (((threeWidthFamily O).mem_applyPotentialPart_idData_iff (by simp [threeWidthFamily])).2 rfl)

/-- **The identity chain's transport is the identity**, at every stage. -/
theorem test_identity_chain_transport (hOE : O ⊆ E) (k x : ℕ) :
    x ∈ ((identityChain O).toChain (identityChain_nonempty O) hOE (ComputableIn.const 0)
      (ComputableIn.const _)).transportTo 0 (0 + k) x := by
  obtain ⟨δ, hδ⟩ := Part.dom_iff_mem.1 ((identityChain O).foldData_dom 0 k)
  exact ((identityChain O).mem_transportTo_iff_applyPotentialPart _ hOE _ _ 0 k hδ
    (by simp [threeWidthFamily])).2 (test_identity_fold O k hδ x)

end Fixture

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.test_nonempty_propagates
#assert_standard_axioms FirstOrder.Language.test_stage_domain
#assert_standard_axioms FirstOrder.Language.test_step_is_realizer
#assert_standard_axioms FirstOrder.Language.test_chain_step
#assert_standard_axioms FirstOrder.Language.test_uniform_evaluators
#assert_standard_axioms FirstOrder.Language.test_fold_actual
#assert_standard_axioms FirstOrder.Language.test_fold_halts
#assert_standard_axioms FirstOrder.Language.test_transport_identification
#assert_standard_axioms FirstOrder.Language.test_identity_fold
#assert_standard_axioms FirstOrder.Language.test_identity_chain_transport
