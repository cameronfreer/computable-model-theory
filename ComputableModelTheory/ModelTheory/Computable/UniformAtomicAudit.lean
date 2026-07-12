/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.UniformAtomic
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for bounded atomic data and its uniform realization

Named acceptance tests for validity, uniform realization, and the central semantic
bridge, checked by `#assert_standard_axioms`. Outside the root import spine; CI checks
it explicitly with

```
lake env lean ComputableModelTheory/ModelTheory/Computable/UniformAtomicAudit.lean
```
-/

open Encodable FirstOrder Language

section

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

omit [L.EffectiveLanguage] in
/-- The validity scan decides validity. -/
theorem test_validAtBool_iff (k : ℕ) (d : AtomicData L ℕ) :
    AtomicData.validAtBool k d = true ↔ AtomicData.ValidAt k d :=
  AtomicData.validAtBool_iff k d

/-- The validity scan is primitive recursive uniformly in the width. -/
theorem test_primrec_validAtBool : Primrec₂ (AtomicData.validAtBool (L := L)) :=
  AtomicData.primrec₂_validAtBool

omit [L.EffectiveLanguage] in
/-- Relabeling along `Fin.val` produces bounded-variable data. -/
theorem test_varsBelow_relabel {k : ℕ} (t : L.Term (Fin k)) :
    Term.VarsBelow k (t.relabel Fin.val) :=
  Term.varsBelow_relabel_val t

/-- Uniform atomic-data realization is oracle-computable. -/
theorem test_realizeAtomicData_computablePredIn (K : ComputableAgeIn O L) :
    ComputablePredIn O fun p : (ℕ × Tuple ℕ) × AtomicData L ℕ ↦
      K.realizeAtomicData p.1.1 p.1.2 p.2 :=
  K.realizeAtomicData_computablePredIn

/-- The central semantic bridge: atomic equivalence is agreement on all valid atomic
data, in both directions. -/
theorem test_bridge (K : ComputableAgeIn O L) (i j : ℕ) (a b : Tuple ℕ)
    (hb : b.length = a.length) :
    (@AtomicEquivalent L ℕ ℕ (K.structureAt i) (K.structureAt j) _
      a.view fun x ↦ b.view (Fin.cast hb.symm x)) ↔
    ∀ d : AtomicData L ℕ, AtomicData.ValidAt a.length d →
      (K.realizeAtomicData i a d ↔ K.realizeAtomicData j b d) :=
  K.atomicEquivalent_iff_forall_validAtomicData i j a b hb

/-- Relabeled terms evaluate to ordinary realization at the cast view. -/
theorem test_termRealize_relabel_view (K : ComputableAgeIn O L) (i : ℕ)
    (env : Tuple ℕ) {k : ℕ} (hk : env.length = k) (t : L.Term (Fin k)) :
    K.termRealize ((i, env), t.relabel Fin.val) =
      @Term.realize L ℕ (K.structureAt i) _
        (fun x : Fin k ↦ env.view (Fin.cast hk.symm x)) t :=
  K.termRealize_relabel_view i env hk t

end

section ConcreteValidity

/-- A variable below the width is valid equality data. -/
theorem test_valid_concrete :
    AtomicData.ValidAt (L := succLang) 1 (Sum.inl (Term.var 0, Term.var 0)) := by
  rw [← AtomicData.validAtBool_iff]
  rfl

/-- A variable at the width is invalid. -/
theorem test_invalid_concrete :
    ¬AtomicData.ValidAt (L := succLang) 1 (Sum.inl (Term.var 1, Term.var 0)) := by
  rw [← AtomicData.validAtBool_iff]
  simp [AtomicData.validAtBool, Term.varsBelowBool, Term.listEncode]

end ConcreteValidity

#assert_standard_axioms test_validAtBool_iff
#assert_standard_axioms test_primrec_validAtBool
#assert_standard_axioms test_varsBelow_relabel
#assert_standard_axioms test_realizeAtomicData_computablePredIn
#assert_standard_axioms test_bridge
#assert_standard_axioms test_termRealize_relabel_view
#assert_standard_axioms test_valid_concrete
#assert_standard_axioms test_invalid_concrete
