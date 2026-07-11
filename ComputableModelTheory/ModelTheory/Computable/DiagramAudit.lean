/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.Diagram
import ComputableModelTheory.ModelTheory.Computable.GraphExample
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for computable diagrams

Named acceptance tests for the signed atomic and quantifier-free diagram predicates
and their computability, checked by `#assert_standard_axioms`. Outside the root import
spine; CI checks it explicitly with

```
lake env lean ComputableModelTheory/ModelTheory/Computable/DiagramAudit.lean
```
-/

open Encodable FirstOrder Language Language.BoundedFormula

section

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage] [L.Structure ℕ] {k : ℕ}
variable [IsComputableStructureIn O L]

/-- The positive atomic diagram of a computable structure is computable in the
oracle. -/
theorem test_posAtomicDiagram : ComputablePredIn O (posAtomicDiagram L k) :=
  posAtomicDiagram_computablePredIn O

/-- The negative atomic diagram of a computable structure is computable in the
oracle. -/
theorem test_negAtomicDiagram : ComputablePredIn O (negAtomicDiagram L k) :=
  negAtomicDiagram_computablePredIn O

/-- The complete atomic diagram of a computable structure is computable in the
oracle. -/
theorem test_completeAtomicDiagram : ComputablePredIn O (completeAtomicDiagram L k) :=
  completeAtomicDiagram_computablePredIn O

/-- The positive quantifier-free diagram of a computable structure is computable in
the oracle. -/
theorem test_posQFDiagram : ComputablePredIn O (posQFDiagram L k) :=
  posQFDiagram_computablePredIn O

/-- The negative quantifier-free diagram of a computable structure is computable in
the oracle. -/
theorem test_negQFDiagram : ComputablePredIn O (negQFDiagram L k) :=
  negQFDiagram_computablePredIn O

/-- The complete quantifier-free diagram of a computable structure is computable in
the oracle. -/
theorem test_completeQFDiagram : ComputablePredIn O (completeQFDiagram L k) :=
  completeQFDiagram_computablePredIn O

end

section ConcreteDiagram

/-- The adjacency formula of the graph language on two variables. -/
private def adjForm : Language.graph.Formula (Fin 2) :=
  BoundedFormula.rel .adj ![Term.var (Sum.inl 0), Term.var (Sum.inl 1)]

attribute [local instance] pathGraphStructure

/-- An adjacent pair lies in the positive atomic diagram of the path graph. -/
theorem test_posAtomicDiagram_member :
    posAtomicDiagram Language.graph 2 (adjForm, ![2, 3]) :=
  ⟨IsAtomic.rel _ _, by
    rw [Formula.Realize]
    exact realize_rel.2 (Or.inl rfl)⟩

/-- A non-adjacent pair lies in the negative atomic diagram of the path graph. -/
theorem test_negAtomicDiagram_member :
    negAtomicDiagram Language.graph 2 (adjForm, ![2, 4]) :=
  ⟨IsAtomic.rel _ _, fun h ↦ by
    rw [Formula.Realize] at h
    rcases realize_rel.1 h with h2 | h2 <;> simp at h2⟩

/-- A positively signed adjacent pair lies in the complete atomic diagram of the path
graph. -/
theorem test_completeAtomicDiagram_pos :
    completeAtomicDiagram Language.graph 2
      (true, ⟨adjForm, IsAtomic.rel _ _⟩, ![2, 3]) :=
  iff_of_true rfl (by
    rw [Formula.Realize]
    exact realize_rel.2 (Or.inl rfl))

/-- A negatively signed non-adjacent pair lies in the complete atomic diagram of the
path graph. -/
theorem test_completeAtomicDiagram_neg :
    completeAtomicDiagram Language.graph 2
      (false, ⟨adjForm, IsAtomic.rel _ _⟩, ![2, 4]) :=
  iff_of_false Bool.false_ne_true fun h ↦ by
    rw [Formula.Realize] at h
    rcases realize_rel.1 h with h2 | h2 <;> simp at h2

end ConcreteDiagram

#assert_standard_axioms test_posAtomicDiagram
#assert_standard_axioms test_negAtomicDiagram
#assert_standard_axioms test_completeAtomicDiagram
#assert_standard_axioms test_posQFDiagram
#assert_standard_axioms test_negQFDiagram
#assert_standard_axioms test_completeQFDiagram
#assert_standard_axioms test_posAtomicDiagram_member
#assert_standard_axioms test_negAtomicDiagram_member
#assert_standard_axioms test_completeAtomicDiagram_pos
#assert_standard_axioms test_completeAtomicDiagram_neg
