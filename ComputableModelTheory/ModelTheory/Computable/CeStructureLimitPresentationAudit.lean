/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.CeStructureLimitPresentation
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: the Level-1 extensional limit presentation

The row that records the design is `test_funMap_always_accepted`: **every** function application
returns an accepted code, including applications to codes that name nothing. That is why no
defensive guard belongs in the structure, and why the carrier hypotheses in the three presentation
laws do no computational work. Without this row, a later reader could reasonably add a guard and
find that everything still compiles.

`test_limitPresentation_domain` pins the carrier as exactly the accepted codes — no membership test
in the enumeration and no fallback value, since canonicalization's range *is* the accepted set.

The last two rows are the semantic interface. Everything above this file should reach the limit
through them, leaving `Part.get` and the evaluator internals below the boundary.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

namespace CeStructureChainIn

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable (D : CeStructureChainIn O L)

/-- **Every function application returns an accepted code**, unconditionally. -/
theorem test_funMap_always_accepted {n : ℕ} (f : L.Functions n) (v : Fin n → ℕ) :
    D.toDomainChain.Accepted (@Structure.funMap L ℕ D.limitStr n f v) :=
  D.accepted_limitStr_funMap f v

/-- **The carrier is exactly the accepted codes** — enumerated with no test and no fallback. -/
theorem test_limitPresentation_domain (U : D.UniformEvaluatorsIn) :
    (D.limitPresentation U).domain = {n | D.toDomainChain.Accepted n} ∧
      (D.limitPresentation U).enum = D.toDomainChain.canonicalRaw :=
  ⟨D.limitPresentation_domain U, rfl⟩

/-- The presentation carries the limit structure. -/
theorem test_limitPresentation_str (U : D.UniformEvaluatorsIn) :
    (D.limitPresentation U).str = D.limitStr :=
  rfl

/-! ### The semantic interface -/

/-- Function values are the limit's, on the arguments' classes. -/
theorem test_funMap_limFunGraph {n : ℕ} (f : L.Functions n) (v : Fin n → ℕ) :
    D.LimFunGraph f (fun k ↦ D.toDomainChain.rawRep (v k))
      (D.toDomainChain.rawRep (@Structure.funMap L ℕ D.limitStr n f v)) :=
  D.limitStr_funMap_limFunGraph f v

/-- Relations are the limit's. -/
theorem test_relMap_iff_limRelHolds {n : ℕ} (R : L.Relations n) (v : Fin n → ℕ) :
    @Structure.RelMap L ℕ D.limitStr n R v ↔
      D.LimRelHolds R fun k ↦ D.toDomainChain.rawRep (v k) :=
  D.limitStr_relMap_iff_limRelHolds R v

end CeStructureChainIn

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.test_funMap_always_accepted
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.test_limitPresentation_domain
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.test_limitPresentation_str
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.test_funMap_limFunGraph
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.test_relMap_iff_limRelHolds
