/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.AtomicSatisfaction
import ComputableModelTheory.ModelTheory.Computable.GraphExample
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for computable atomic satisfaction

Named acceptance tests for the atomic-data extractor and the atomic-satisfaction
contracts, checked by `#assert_standard_axioms`. Outside the root import spine; CI
checks it explicitly with

```
lake env lean ComputableModelTheory/ModelTheory/Computable/AtomicSatisfactionAudit.lean
```
-/

open Encodable FirstOrder Language Language.BoundedFormula

section

variable {O : Set (ℕ →. ℕ)} {L : Language} {α : Type*} [Primcodable α]
variable [L.EffectiveLanguage] [L.Structure ℕ] {k : ℕ}

omit [Primcodable α] [L.EffectiveLanguage] [L.Structure ℕ] in
/-- The extractor succeeds exactly on atomic formulas. -/
theorem test_atomicData?_isSome_iff (φ : L.Formula α) :
    (atomicData? φ).isSome ↔ (φ : L.BoundedFormula α 0).IsAtomic :=
  atomicData?_isSome_iff φ

omit [Primcodable α] [L.EffectiveLanguage] [L.Structure ℕ] in
/-- The extractor computes the equality data. -/
theorem test_atomicData?_equal (t₁ t₂ : L.Term (α ⊕ Fin 0)) :
    atomicData? (BoundedFormula.equal t₁ t₂ : L.Formula α) =
      some (Sum.inl (t₁.relabel (Sum.elim id Fin.elim0),
        t₂.relabel (Sum.elim id Fin.elim0))) :=
  atomicData?_eq_some_of_equal t₁ t₂

omit [Primcodable α] [L.EffectiveLanguage] [L.Structure ℕ] in
/-- The extractor computes the relation data. -/
theorem test_atomicData?_rel {n : ℕ} (R : L.Relations n)
    (ts : Fin n → L.Term (α ⊕ Fin 0)) :
    atomicData? (BoundedFormula.rel R ts : L.Formula α) =
      some (Sum.inr ((⟨n, R⟩ : L.RelationSymbol),
        (List.finRange n).map fun i ↦ (ts i).relabel (Sum.elim id Fin.elim0))) :=
  atomicData?_eq_some_of_rel R ts

omit [L.Structure ℕ] in
/-- The extractor is computable. -/
theorem test_computable_atomicData? : Computable (atomicData? (L := L) (α := α)) :=
  computable_atomicData?

/-- The roadmap PR 7 gate in diagram-ready total form: atomicity together with
satisfaction is a computable predicate, deciding `false` off the atomic fragment. -/
theorem test_atomic_realize [IsComputableStructureIn O L] :
    ComputablePredIn O fun p : L.Formula (Fin k) × (Fin k → ℕ) ↦
      (p.1 : L.BoundedFormula (Fin k) 0).IsAtomic ∧ p.1.Realize p.2 :=
  atomic_realize_computablePredIn O k

/-- The uniform subtype form: satisfaction of atomic formulas is a computable
predicate. -/
theorem test_atomicFormula_realize [IsComputableStructureIn O L] :
    ComputablePredIn O
      fun p : { φ : L.Formula (Fin k) //
          (φ : L.BoundedFormula (Fin k) 0).IsAtomic } × (Fin k → ℕ) ↦
      (p.1 : L.Formula (Fin k)).Realize p.2 :=
  atomicFormula_realize_computablePredIn O k

/-- The pointwise corollary: satisfaction of a fixed atomic formula is a computable
predicate on tuples. -/
theorem test_realize_pointwise [IsComputableStructureIn O L] (φ : L.Formula (Fin k))
    (hφ : (φ : L.BoundedFormula (Fin k) 0).IsAtomic) :
    ComputablePredIn O fun v : Fin k → ℕ ↦ φ.Realize v :=
  realize_computablePredIn_of_isAtomic O φ hφ

end

section ConcreteDispatch

/-- A two-variable equality over the empty language. -/
private def eqForm : Language.empty.Formula (Fin 2) :=
  BoundedFormula.equal (Term.var (Sum.inl 0)) (Term.var (Sum.inl 1))

attribute [local instance] FirstOrder.Language.emptyStructure

private instance :
    DecidablePred (RelationApplicationData.relMap (L := Language.empty) (M := ℕ)) :=
  fun d ↦ isEmptyElim d

/-- Dispatch semantics: the equality branch accepts a true equation. -/
theorem test_atomicSatBool_equal_true :
    atomicSatBool (eqForm, ![3, 3]) = true :=
  (atomicSatBool_iff _).2 ⟨BoundedFormula.IsAtomic.equal _ _, by
    rw [Formula.Realize]
    exact (BoundedFormula.realize_bdEqual _ _).2 rfl⟩

/-- Dispatch semantics: the equality branch rejects a false equation. -/
theorem test_atomicSatBool_equal_false :
    atomicSatBool (eqForm, ![3, 4]) = false := by
  refine Bool.eq_false_iff.2 fun hB ↦ ?_
  have h := ((atomicSatBool_iff _).1 hB).2
  rw [Formula.Realize] at h
  have h2 := (BoundedFormula.realize_bdEqual _ _).1 h
  simp at h2

/-- The adjacency formula of the graph language on two variables. -/
private def adjForm : Language.graph.Formula (Fin 2) :=
  BoundedFormula.rel .adj ![Term.var (Sum.inl 0), Term.var (Sum.inl 1)]

section

attribute [local instance] pathGraphStructure

/-- Dispatch semantics: the relation branch accepts an adjacent pair of the path
graph. -/
theorem test_atomicSatBool_rel_true :
    atomicSatBool (adjForm, ![2, 3]) = true :=
  (atomicSatBool_iff _).2 ⟨BoundedFormula.IsAtomic.rel _ _, by
    rw [Formula.Realize]
    exact BoundedFormula.realize_rel.2 (Or.inl rfl)⟩

/-- Dispatch semantics: the relation branch rejects a non-adjacent pair of the path
graph. -/
theorem test_atomicSatBool_rel_false :
    atomicSatBool (adjForm, ![2, 4]) = false := by
  refine Bool.eq_false_iff.2 fun hB ↦ ?_
  have h := ((atomicSatBool_iff _).1 hB).2
  rw [Formula.Realize] at h
  have h2 := BoundedFormula.realize_rel.1 h
  rcases h2 with h2 | h2 <;> simp at h2

end

end ConcreteDispatch

#assert_standard_axioms test_atomicSatBool_equal_true
#assert_standard_axioms test_atomicSatBool_equal_false
#assert_standard_axioms test_atomicSatBool_rel_true
#assert_standard_axioms test_atomicSatBool_rel_false
#assert_standard_axioms test_atomicData?_isSome_iff
#assert_standard_axioms test_atomicData?_equal
#assert_standard_axioms test_atomicData?_rel
#assert_standard_axioms test_computable_atomicData?
#assert_standard_axioms test_atomic_realize
#assert_standard_axioms test_atomicFormula_realize
#assert_standard_axioms test_realize_pointwise
