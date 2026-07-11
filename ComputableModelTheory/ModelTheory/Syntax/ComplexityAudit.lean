/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Syntax.Complexity
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for formula-complexity computability

Named acceptance tests for the `IsAtomic`/`IsQF` deciders and their computability,
checked by `#assert_standard_axioms`. Outside the root import spine; CI checks it
explicitly with

```
lake env lean ComputableModelTheory/ModelTheory/Syntax/ComplexityAudit.lean
```
-/

open Encodable FirstOrder Language Language.BoundedFormula

section

variable {L : Language} {α : Type*} {n : ℕ} [Primcodable α] [L.EffectiveLanguage]

omit [Primcodable α] [L.EffectiveLanguage] in
/-- The Boolean decider decides `IsAtomic`. -/
theorem test_isAtomicBool_iff (φ : L.BoundedFormula α n) :
    isAtomicBool φ = true ↔ φ.IsAtomic :=
  isAtomicBool_iff φ

omit [Primcodable α] [L.EffectiveLanguage] in
/-- The Boolean decider decides `IsQF`. -/
theorem test_isQFBool_iff (φ : L.BoundedFormula α n) : isQFBool φ = true ↔ φ.IsQF :=
  isQFBool_iff φ

omit [Primcodable α] [L.EffectiveLanguage] in
/-- `IsAtomic` is decidable. -/
@[reducible] def test_isAtomic_decidable :
    DecidablePred (IsAtomic : L.BoundedFormula α n → Prop) :=
  inferInstance

omit [Primcodable α] [L.EffectiveLanguage] in
/-- `IsQF` is decidable. -/
@[reducible] def test_isQF_decidable : DecidablePred (IsQF : L.BoundedFormula α n → Prop) :=
  inferInstance

/-- Atomicity of packaged bounded formulas is a computable predicate. -/
theorem test_computablePred_isAtomic :
    ComputablePred fun s : Σ n, L.BoundedFormula α n ↦ s.2.IsAtomic :=
  computablePred_isAtomic

/-- The roadmap acceptance gate: quantifier-freeness of packaged bounded formulas is a
computable predicate. -/
theorem test_computablePred_isQF :
    ComputablePred fun s : Σ n, L.BoundedFormula α n ↦ s.2.IsQF :=
  computablePred_isQF

end

#assert_standard_axioms test_isAtomicBool_iff
#assert_standard_axioms test_isQFBool_iff
#assert_standard_axioms test_isAtomic_decidable
#assert_standard_axioms test_isQF_decidable
#assert_standard_axioms test_computablePred_isAtomic
#assert_standard_axioms test_computablePred_isQF
