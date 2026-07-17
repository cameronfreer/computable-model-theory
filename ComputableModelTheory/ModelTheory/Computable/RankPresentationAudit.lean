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
`RecursiveIn` fields, not extensional existence claims — and the on-domain
specifications hold: the function evaluator halts with a rank of the source-side
interpretation, and the relation decider halts with the source-side verdict.
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

end

#assert_standard_axioms test_rank_evaluators_recursiveIn
#assert_standard_axioms test_rankFunEval_spec
#assert_standard_axioms test_rankRelEval_spec
