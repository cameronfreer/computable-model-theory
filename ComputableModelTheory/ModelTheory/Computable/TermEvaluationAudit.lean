/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.TermEvaluation
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for computable term evaluation

Named acceptance tests for the value-stack machine and computable term evaluation,
checked by `#assert_standard_axioms`. Outside the root import spine; CI checks it
explicitly with

```
lake env lean ComputableModelTheory/ModelTheory/Computable/TermEvaluationAudit.lean
```
-/

open Encodable FirstOrder Language Language.Term

section

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage] [L.Structure ℕ] {m : ℕ}

/-- The machine bridge: the value stack computes the realizations of the decoded
terms. -/
theorem test_valueStack_eq_map_realize (env : Fin m → ℕ)
    (l : List (Fin m ⊕ (Σ i, L.Functions i))) :
    valueStack env l = (Term.listDecode l).map fun t ↦ t.realize env :=
  valueStack_eq_map_realize env l

/-- The roadmap PR 7 gate: term evaluation in a computable structure is computable in
the oracle. -/
theorem test_realize_computableIn [IsComputableStructureIn O L] :
    ComputableIn O fun p : L.Term (Fin m) × (Fin m → ℕ) ↦ p.1.realize p.2 :=
  realize_computableIn O

/-- Semantic equation: evaluating a variable reads the environment. -/
theorem test_realize_var_value :
    (Term.var (2 : Fin 3) : Language.empty.Term (Fin 3)).realize
      (M := ℕ) ![4, 5, 6] = 6 :=
  rfl

end

#assert_standard_axioms test_valueStack_eq_map_realize
#assert_standard_axioms test_realize_computableIn
#assert_standard_axioms test_realize_var_value
