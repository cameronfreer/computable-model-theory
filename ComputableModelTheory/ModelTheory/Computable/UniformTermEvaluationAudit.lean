/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.UniformTermEvaluation
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for uniform term evaluation

Named acceptance tests for the age-indexed term evaluator, checked by
`#assert_standard_axioms`. Outside the root import spine; CI checks it explicitly with

```
lake env lean ComputableModelTheory/ModelTheory/Computable/UniformTermEvaluationAudit.lean
```
-/

open Encodable FirstOrder Language

section

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-- The uniform evaluator is oracle-computable. -/
theorem test_termRealize_computableIn (K : ComputableAgeIn O L) :
    ComputableIn O K.termRealize :=
  K.termRealize_computableIn

/-- The machine equation with ordinary realization. -/
theorem test_termValueStack_eq (K : ComputableAgeIn O L) (i : ℕ) (env : Tuple ℕ)
    (l : List (ℕ ⊕ (Σ j, L.Functions j))) :
    K.termValueStack i env l =
      (Term.listDecode l).map fun t ↦
        @Term.realize L ℕ (K.structureAt i) ℕ (ComputableAgeIn.envFun env) t :=
  K.termValueStack_eq_map_realize i env l

end

section ConcreteEvaluation

/-- Variable lookup in range. -/
theorem test_envFun_in_range :
    ComputableAgeIn.envFun [5, 7] 1 = 7 :=
  rfl

/-- Default lookup out of range. -/
theorem test_envFun_out_of_range :
    ComputableAgeIn.envFun [5, 7] 9 = 0 :=
  rfl

/-- A function-symbol branch in the successor age: evaluating `succ (var 0)` under the
environment `[4]` at any index yields `5`. -/
theorem test_succAge_termRealize (O : Set (ℕ →. ℕ)) :
    (succAge O).termRealize ((0, [4]),
      Term.func SuccFunctions.succ ![Term.var 0]) = 5 :=
  rfl

/-- Semantic equality with ordinary realization at a fixed index. -/
theorem test_succAge_termRealize_eq_realize (O : Set (ℕ →. ℕ)) :
    (succAge O).termRealize ((0, [4]), Term.var 0) =
      @Term.realize succLang ℕ ((succAge O).structureAt 0) ℕ
        (ComputableAgeIn.envFun [4]) (Term.var 0) :=
  rfl

end ConcreteEvaluation

#assert_standard_axioms test_termRealize_computableIn
#assert_standard_axioms test_termValueStack_eq
#assert_standard_axioms test_envFun_in_range
#assert_standard_axioms test_envFun_out_of_range
#assert_standard_axioms test_succAge_termRealize
#assert_standard_axioms test_succAge_termRealize_eq_realize
