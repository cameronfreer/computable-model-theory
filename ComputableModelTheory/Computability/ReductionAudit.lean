/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.Reduction
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for reductions and oracle transport

Named acceptance tests for `predOracle`, `PredTuringReducible`, and the transport lemmas,
checked by `#assert_standard_axioms` (defined in the oracle-predicate audit). Outside the
root import spine; CI checks it explicitly with

```
lake env lean ComputableModelTheory/Computability/ReductionAudit.lean
```
-/

section

variable {α β : Type*} [Primcodable α] [Primcodable β] {O₁ O₂ : Set (ℕ →. ℕ)}
  {p : α → Prop} {q : β → Prop}

/-- A predicate is computable in its own characteristic oracle. -/
theorem test_predOracle_self (p : α → Prop) [DecidablePred p] :
    ComputablePredIn {predOracle p} p :=
  computablePredIn_predOracle_self p

set_option linter.unusedDecidableInType false in
/-- Predicate Turing reducibility is reflexive. -/
theorem test_predTuringReducible_refl (p : α → Prop) [DecidablePred p] :
    PredTuringReducible p p :=
  PredTuringReducible.refl p

/-- Transport of predicate computability along relative computation of oracles. -/
theorem test_transport (hO : ∀ g ∈ O₁, RecursiveIn O₂ g) (hp : ComputablePredIn O₁ p) :
    ComputablePredIn O₂ p :=
  computablePredIn_of_oracle_transport hO hp

/-- Transport of enumerability along relative computation of oracles. -/
theorem test_re_transport (hO : ∀ g ∈ O₁, RecursiveIn O₂ g) (hp : REPredIn O₁ p) :
    REPredIn O₂ p :=
  rePredIn_of_oracle_transport hO hp

/-- Reducibility statements compose with the predicate layer: a predicate reducible to a
decidable `q` inherits Boolean closure relative to the same oracle. -/
theorem test_reducible_and_not (h : PredTuringReducible p q) :
    ∃ _ : DecidablePred q, ComputablePredIn {predOracle q} fun a ↦ p a ∧ ¬p a := by
  obtain ⟨D, h⟩ := h
  exact ⟨D, h.and h.not⟩

end

#assert_standard_axioms test_predOracle_self
#assert_standard_axioms test_predTuringReducible_refl
#assert_standard_axioms test_transport
#assert_standard_axioms test_re_transport
#assert_standard_axioms test_reducible_and_not
