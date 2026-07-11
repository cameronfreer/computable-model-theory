/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.QFSatisfaction
import ComputableModelTheory.ModelTheory.Computable.GraphExample
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for computable quantifier-free satisfaction

Named acceptance tests for the satisfaction stack machine and the quantifier-free
satisfaction decider, checked by `#assert_standard_axioms`. Outside the root import
spine; CI checks it explicitly with

```
lake env lean ComputableModelTheory/ModelTheory/Computable/QFSatisfactionAudit.lean
```
-/

open Encodable FirstOrder Language Language.BoundedFormula

section

variable {L : Language} [L.EffectiveLanguage] [L.Structure ℕ] {k : ℕ}
variable [DecidablePred (RelationApplicationData.relMap (L := L) (M := ℕ))]

omit [L.EffectiveLanguage] in
/-- The machine computes the specification payloads of mathlib's decoder. -/
theorem test_satStack_bridge (v : Fin k → ℕ) (l : List (FormulaSymbol L (Fin k))) :
    satStack v l = (BoundedFormula.listDecode l).map (flagOf v) :=
  satStack_eq_map_listDecode v l

omit [L.EffectiveLanguage] in
/-- The decider decides quantifier-freeness together with satisfaction. -/
theorem test_qfSatBool_iff (p : L.Formula (Fin k) × (Fin k → ℕ)) :
    qfSatBool p = true ↔ (p.1 : L.BoundedFormula (Fin k) 0).IsQF ∧ p.1.Realize p.2 :=
  qfSatBool_iff p

end

section ConcreteQF

/-- A two-variable equality over the empty language. -/
private def eqForm : Language.empty.Formula (Fin 2) :=
  BoundedFormula.equal (Term.var (Sum.inl 0)) (Term.var (Sum.inl 1))

attribute [local instance] FirstOrder.Language.emptyStructure

private instance :
    DecidablePred (RelationApplicationData.relMap (L := Language.empty) (M := ℕ)) :=
  fun d ↦ isEmptyElim d

/-- The equality leaf accepts a true equation. -/
theorem test_qfSatBool_equal_true : qfSatBool (eqForm, ![3, 3]) = true :=
  (qfSatBool_iff _).2 ⟨(IsAtomic.equal _ _).isQF, by
    rw [Formula.Realize]
    exact (BoundedFormula.realize_bdEqual _ _).2 rfl⟩

/-- The equality leaf rejects a false equation. -/
theorem test_qfSatBool_equal_false : qfSatBool (eqForm, ![3, 4]) = false := by
  refine Bool.eq_false_iff.2 fun hB ↦ ?_
  have h := ((qfSatBool_iff _).1 hB).2
  rw [Formula.Realize] at h
  have h2 := (BoundedFormula.realize_bdEqual _ _).1 h
  simp at h2

/-- An implication with a false antecedent is satisfied. -/
theorem test_qfSatBool_imp_true :
    qfSatBool ((eqForm.imp falsum : Language.empty.Formula (Fin 2)), ![3, 4]) = true :=
  (qfSatBool_iff _).2 ⟨IsQF.imp (IsAtomic.equal _ _).isQF IsQF.falsum, by
    rw [Formula.Realize]
    refine BoundedFormula.realize_imp.2 fun h ↦ ?_
    have h2 := (BoundedFormula.realize_bdEqual _ _).1 h
    simp at h2⟩

/-- The falsum leaf is decided `false`. -/
theorem test_qfSatBool_falsum :
    qfSatBool ((falsum : Language.empty.Formula (Fin 0)), ![]) = false := by
  refine Bool.eq_false_iff.2 fun hB ↦ ?_
  have h := ((qfSatBool_iff _).1 hB).2
  rw [Formula.Realize] at h
  exact h

/-- The decider is `false` off the quantifier-free fragment: a quantified formula is
rejected. -/
theorem test_qfSatBool_rejects_all :
    qfSatBool (((BoundedFormula.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 0))).all :
      Language.empty.Formula (Fin 0)), ![]) = false := by
  refine Bool.eq_false_iff.2 fun hB ↦ ?_
  have h := ((qfSatBool_iff _).1 hB).1
  have h2 := (isQFBool_iff _).2 h
  simp [isQFBool] at h2

/-- The adjacency formula of the graph language on two variables. -/
private def adjForm : Language.graph.Formula (Fin 2) :=
  BoundedFormula.rel .adj ![Term.var (Sum.inl 0), Term.var (Sum.inl 1)]

section

attribute [local instance] pathGraphStructure

/-- The relation leaf accepts an adjacent pair of the path graph. -/
theorem test_qfSatBool_rel_true : qfSatBool (adjForm, ![2, 3]) = true :=
  (qfSatBool_iff _).2 ⟨(IsAtomic.rel _ _).isQF, by
    rw [Formula.Realize]
    exact BoundedFormula.realize_rel.2 (Or.inl rfl)⟩

/-- The relation leaf rejects a non-adjacent pair of the path graph. -/
theorem test_qfSatBool_rel_false : qfSatBool (adjForm, ![2, 4]) = false := by
  refine Bool.eq_false_iff.2 fun hB ↦ ?_
  have h := ((qfSatBool_iff _).1 hB).2
  rw [Formula.Realize] at h
  have h2 := BoundedFormula.realize_rel.1 h
  rcases h2 with h2 | h2 <;> simp at h2

end

end ConcreteQF

#assert_standard_axioms test_satStack_bridge
#assert_standard_axioms test_qfSatBool_iff
#assert_standard_axioms test_qfSatBool_equal_true
#assert_standard_axioms test_qfSatBool_equal_false
#assert_standard_axioms test_qfSatBool_imp_true
#assert_standard_axioms test_qfSatBool_falsum
#assert_standard_axioms test_qfSatBool_rejects_all
#assert_standard_axioms test_qfSatBool_rel_true
#assert_standard_axioms test_qfSatBool_rel_false
