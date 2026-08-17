/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.CeStructureLimitEval
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: the evaluators of the uncertified Level-1 limit

Two rows carry the design and are worth stating even though they read as small.

**Halting is unconditional** — no `Accepted` guard, on either pipeline. Evaluation is defined on
*every* coded argument tuple, because every natural number's `rawRep` is valid; acceptedness is a
fact about which codes name limit elements, not a precondition for computing with them. A guard
added defensively later would typecheck and quietly narrow the evaluators.

**Returned function codes are accepted**, and this is proved from `canonicalPart` alone —
independently of any later carrier-closure theorem. Deriving it from closure instead would make the
presentation's `domain_closed` circular.

The nullary rows pin the arity-zero boundary: the common stage of an empty argument list is `0`, so
constants and nullary relations are evaluated once, at stage `0`, with an empty traversal.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

namespace CeStructureChainIn

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable (D : CeStructureChainIn O L)

/-- **Unconditional halting, function side.** -/
theorem test_rawFunEvalPart_dom (d : FunctionApplicationData L ℕ) : (D.rawFunEvalPart d).Dom :=
  D.rawFunEvalPart_dom d

/-- **Unconditional halting, relation side.** -/
theorem test_rawRelEvalPart_dom (d : RelationApplicationData L ℕ) : (D.rawRelEvalPart d).Dom :=
  D.rawRelEvalPart_dom d

/-- **Returned function codes are accepted**, from `canonicalPart` alone. -/
theorem test_accepted_of_mem_rawFunEvalPart {d : FunctionApplicationData L ℕ} {c : ℕ}
    (hc : c ∈ D.rawFunEvalPart d) : D.toDomainChain.Accepted c :=
  accepted_of_mem_rawFunEvalPart hc

/-- The named raw output is a valid representative — the one fact that buys both the final
canonicalization's halting and the semantic theorem. -/
theorem test_limMem_rawFunOutput {d : FunctionApplicationData L ℕ} {src : List ℕ}
    (hsrc : src ∈ D.toDomainChain.transportRawArgsPart d.argsList)
    {hlen : src.length = (d.toSymbol).arity} {y : ℕ}
    (hy : y ∈ (D.stageAt (D.argStage d.argsList)).funEval
      (FunctionApplicationData.equivSubtype.symm ⟨(d.toSymbol, src), hlen⟩)) :
    D.toDomainChain.limMem (D.argStage d.argsList, y) :=
  limMem_rawFunOutput hsrc hy

/-! ### The semantics -/

/-- **Function soundness**: a returned code names the limit's value of the symbol at the arguments'
classes. One-way on purpose — an accepted-code `iff` is derivable from `limFunGraph_functional` and
`accepted_limEquiv_iff`, and nothing needs it yet. -/
theorem test_limFunGraph_of_mem_rawFunEvalPart {d : FunctionApplicationData L ℕ} {c : ℕ}
    (hc : c ∈ D.rawFunEvalPart d) :
    D.LimFunGraph d.symbol (fun k ↦ D.toDomainChain.rawRep (d.args k))
      (D.toDomainChain.rawRep c) :=
  limFunGraph_of_mem_rawFunEvalPart hc

/-- **Relation characterization**: the returned truth value is exactly whether the limit relation
holds of the arguments' classes. -/
theorem test_rawRelEvalPart_spec (d : RelationApplicationData L ℕ) :
    ∃ b ∈ D.rawRelEvalPart d,
      (b = true ↔ D.LimRelHolds d.symbol fun k ↦ D.toDomainChain.rawRep (d.args k)) :=
  D.rawRelEvalPart_spec d

/-! ### Arity zero -/

/-- **The common stage of an empty argument list is `0`.** So constants and nullary relations are
evaluated once, at stage `0`. -/
theorem test_argStage_nil : D.argStage [] = 0 := rfl

/-- And the empty traversal returns the empty list, so nothing is transported. -/
theorem test_transport_nil : D.toDomainChain.transportRawArgsPart [] = Part.some [] := rfl

end CeStructureChainIn

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.test_rawFunEvalPart_dom
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.test_rawRelEvalPart_dom
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.test_accepted_of_mem_rawFunEvalPart
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.test_limMem_rawFunOutput
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.test_limFunGraph_of_mem_rawFunEvalPart
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.test_rawRelEvalPart_spec
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.test_argStage_nil
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.test_transport_nil
