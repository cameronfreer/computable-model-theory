/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.AtomicEquivComputability
import ComputableModelTheory.ModelTheory.Computable.GraphExample
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for effective failure of atomic equivalence

Named acceptance tests for the r.e. non-equivalence theorems and a concrete
distinguisher, checked by `#assert_standard_axioms`. Outside the root import spine; CI
checks it explicitly with

```
lake env lean ComputableModelTheory/ModelTheory/Computable/AtomicEquivComputabilityAudit.lean
```
-/

open Encodable FirstOrder Language Language.BoundedFormula

section

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-- Failure of atomic equivalence of fixed tuples of two presentations is r.e. -/
theorem test_not_atomicEquivTuples_rePredIn (P Q : GeneratedPresentationIn O L)
    {k : ℕ} (a b : Fin k → ℕ) :
    REPredIn O fun _ : Unit ↦ ¬P.AtomicEquivTuples Q a b :=
  P.not_atomicEquivTuples_rePredIn Q a b

/-- The generator form for presentations of equal generator length. -/
theorem test_not_atomicEquivGens_rePredIn (P Q : GeneratedPresentationIn O L)
    (h : P.gens.length = Q.gens.length) :
    REPredIn O fun _ : Unit ↦
      ¬P.AtomicEquivTuples Q P.generatorView fun i ↦ Q.generatorView (Fin.cast h i) :=
  P.not_atomicEquivGens_rePredIn Q h

/-- A presentation's tuple is atomically equivalent to itself. -/
theorem test_atomicEquivTuples_refl (P : GeneratedPresentationIn O L) {k : ℕ}
    (a : Fin k → ℕ) : P.AtomicEquivTuples P a a :=
  ⟨fun _ _ ↦ Iff.rfl, fun _ _ ↦ Iff.rfl⟩

end

section ConcreteNonEquivalence

attribute [local instance] pathGraphStructure

/-- A concrete failure of atomic equivalence: an adjacent and a non-adjacent pair of
the path graph are distinguished by the adjacency atom. -/
theorem test_not_atomicEquivalent_concrete :
    ¬AtomicEquivalent Language.graph (M := ℕ) (N := ℕ) ![2, 3] ![2, 4] := by
  intro h
  have h2 := (h.2 .adj ![Term.var 0, Term.var 1]).1 (Or.inl rfl)
  rcases h2 with h2 | h2 <;> simp at h2

end ConcreteNonEquivalence

#assert_standard_axioms test_not_atomicEquivTuples_rePredIn
#assert_standard_axioms test_not_atomicEquivGens_rePredIn
#assert_standard_axioms test_atomicEquivTuples_refl
#assert_standard_axioms test_not_atomicEquivalent_concrete
