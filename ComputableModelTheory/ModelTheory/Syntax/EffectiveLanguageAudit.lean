/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.OraclePred
import ComputableModelTheory.ModelTheory.Syntax.EffectiveLanguage
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for effective languages

Named acceptance tests for `EffectiveLanguage` and the symbol API, checked by
`#assert_standard_axioms`. Outside the root import spine; CI checks it explicitly with

```
lake env lean ComputableModelTheory/ModelTheory/Syntax/EffectiveLanguageAudit.lean
```
-/

open FirstOrder Language

section

variable {L : Language} [L.EffectiveLanguage] {M : Type*}

/-- Symbols of an effective language can be quantified over uniformly, with computable
predicates on their arities: here, that a symbol is at most binary. -/
theorem test_uniform_arity_predicate {O : Set (ℕ →. ℕ)} :
    ComputablePredIn O fun s : L.FunctionSymbol ↦ s.arity ≤ 2 :=
  (ComputablePred.computablePredIn
      (PrimrecPred.computablePred (Primrec.nat_le.comp .id (.const 2)))).comp
    computable_functionSymbol_arity.computableIn

/-- The arity map on function symbols is computable. -/
theorem test_functionSymbol_arity : Computable (FunctionSymbol.arity (L := L)) :=
  computable_functionSymbol_arity

/-- The arity map on relation symbols is computable. -/
theorem test_relationSymbol_arity : Computable (RelationSymbol.arity (L := L)) :=
  computable_relationSymbol_arity

omit [L.EffectiveLanguage] in
/-- Application data round-trips through its sigma packaging. -/
theorem test_applicationData_roundtrip (d : FunctionApplicationData L M) :
    FunctionApplicationData.equivSigma.symm (FunctionApplicationData.equivSigma d) = d :=
  Equiv.symm_apply_apply _ _

/-- The empty language is effective. (`EffectiveLanguage` carries `Primcodable` data, so
this is a `def`.) -/
@[reducible] def test_empty_effective : Language.empty.EffectiveLanguage :=
  inferInstance

end

#assert_standard_axioms test_uniform_arity_predicate
#assert_standard_axioms test_functionSymbol_arity
#assert_standard_axioms test_relationSymbol_arity
#assert_standard_axioms test_applicationData_roundtrip
#assert_standard_axioms test_empty_effective
