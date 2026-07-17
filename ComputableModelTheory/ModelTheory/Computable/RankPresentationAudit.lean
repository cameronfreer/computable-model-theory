/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.RankPresentation
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for the transported rank evaluators

Named acceptance tests for the factored rank evaluators, checked by
`#assert_standard_axioms`. Outside the root import spine; CI checks it via
`scripts/run-audit-modules.sh`.

Coverage: the evaluators are uniformly partial recursive in the oracle — as
`RecursiveIn` fields, not extensional existence claims; the on-domain specifications;
the commuting squares in both encoded and decoded forms plus the relation equivalence;
and the bundled Level-1 presentation whose domain is definitionally the range of
`posRank`.
-/

open Encodable FirstOrder Language

section

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable (P : CePresentationIn O L)

/-- Gate: the transported evaluators are uniformly partial recursive in the oracle. -/
theorem test_rank_evaluators_recursiveIn :
    RecursiveIn O P.rankFunEval ∧ RecursiveIn O P.rankRelEval :=
  ⟨P.rankFunEval_recursiveIn, P.rankRelEval_recursiveIn⟩

/-- Gate (function half of the commuting square, evaluator level): on realized
argument ranks the evaluator halts with a rank of the source-side interpretation. -/
theorem test_rankFunEval_spec (d : FunctionApplicationData L ℕ)
    (src : Fin d.arity → ℕ) (hsrc : ∀ k, src k ∈ P.rankEnum (d.args k)) :
    ∃ y ∈ P.rankOf (@Structure.funMap L ℕ P.str d.arity d.symbol src),
      y ∈ P.rankFunEval d :=
  P.rankFunEval_spec d src hsrc

/-- Gate (relation half of the commuting square, evaluator level): on realized
argument ranks the decider halts with the source-side verdict. -/
theorem test_rankRelEval_spec (d : RelationApplicationData L ℕ)
    (src : Fin d.arity → ℕ) (hsrc : ∀ k, src k ∈ P.rankEnum (d.args k)) :
    ∃ b ∈ P.rankRelEval d,
      (b = true ↔ @Structure.RelMap L ℕ P.str d.arity d.symbol src) :=
  P.rankRelEval_spec d src hsrc

/-- Gate (commuting square, encoded form): the rank structure's interpretation is the
rank of the source interpretation. -/
theorem test_rankStr_funMap_mem_rankOf {n : ℕ} (f : L.Functions n) (v src : Fin n → ℕ)
    (hsrc : ∀ k, src k ∈ P.rankEnum (v k)) :
    @Structure.funMap L ℕ P.rankStr n f v
      ∈ P.rankOf (@Structure.funMap L ℕ P.str n f src) :=
  P.rankStr_funMap_mem_rankOf f v src hsrc

/-- Gate (commuting square, decoded form): decoding the rank structure's output
recovers the source interpretation. -/
theorem test_rankEnum_rankStr_funMap {n : ℕ} (f : L.Functions n) (v src : Fin n → ℕ)
    (hsrc : ∀ k, src k ∈ P.rankEnum (v k)) :
    @Structure.funMap L ℕ P.str n f src
      ∈ P.rankEnum (@Structure.funMap L ℕ P.rankStr n f v) :=
  P.rankEnum_rankStr_funMap f v src hsrc

/-- Gate (commuting square, relations): the rank structure holds a relation exactly
when the source does. -/
theorem test_rankStr_relMap_iff {n : ℕ} (R : L.Relations n) (v src : Fin n → ℕ)
    (hsrc : ∀ k, src k ∈ P.rankEnum (v k)) :
    @Structure.RelMap L ℕ P.rankStr n R v ↔ @Structure.RelMap L ℕ P.str n R src :=
  P.rankStr_relMap_iff R v src hsrc

/-- Gate: the bundled Level-1 rank presentation exists with `posRank` literally as its
enumeration, so its domain is definitionally the range of `posRank`. -/
theorem test_rankPresentation_domain :
    P.rankPresentation.enum = P.posRank ∧
      P.rankPresentation.domain = Set.range P.posRank :=
  ⟨rfl, rfl⟩

end

#assert_standard_axioms test_rank_evaluators_recursiveIn
#assert_standard_axioms test_rankStr_funMap_mem_rankOf
#assert_standard_axioms test_rankEnum_rankStr_funMap
#assert_standard_axioms test_rankStr_relMap_iff
#assert_standard_axioms test_rankPresentation_domain
#assert_standard_axioms test_rankFunEval_spec
#assert_standard_axioms test_rankRelEval_spec
