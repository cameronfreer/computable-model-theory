/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.AtomicEquiv
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for atomic equivalence

Named acceptance tests for atomic equivalence of tuples, checked by
`#assert_standard_axioms`. Outside the root import spine; CI checks it explicitly with

```
lake env lean ComputableModelTheory/ModelTheory/Computable/AtomicEquivAudit.lean
```
-/

open FirstOrder Language Language.BoundedFormula

section

variable {L : Language} {M N P : Type*}
variable [L.Structure M] [L.Structure N] [L.Structure P] {k : ℕ}

/-- Atomic equivalence is reflexive. -/
theorem test_atomicEquivalent_refl (a : Fin k → M) : AtomicEquivalent L a a :=
  AtomicEquivalent.refl a

/-- Atomic equivalence is symmetric. -/
theorem test_atomicEquivalent_symm (a : Fin k → M) (b : Fin k → N)
    (h : AtomicEquivalent L a b) : AtomicEquivalent L b a :=
  h.symm

/-- Atomic equivalence is transitive. -/
theorem test_atomicEquivalent_trans (a : Fin k → M) (b : Fin k → N) (c : Fin k → P)
    (hab : AtomicEquivalent L a b) (hbc : AtomicEquivalent L b c) :
    AtomicEquivalent L a c :=
  hab.trans hbc

/-- The formula characterization: atomic equivalence is agreement on all atomic
formulas. -/
theorem test_atomicEquivalent_iff_formulas (a : Fin k → M) (b : Fin k → N) :
    AtomicEquivalent L a b ↔
      ∀ φ : AtomicFormula L (Fin k),
        ((φ : L.Formula (Fin k)).Realize a ↔ (φ : L.Formula (Fin k)).Realize b) :=
  atomicEquivalent_iff_forall_atomicFormula a b

/-- The closure-equivalence gate: atomic equivalence is the existence of a
generator-preserving equivalence of tuple closures. -/
theorem test_atomicEquivalent_iff_closure_equiv (a : Fin k → M) (b : Fin k → N) :
    AtomicEquivalent L a b ↔
      ∃ e : Substructure.closure L (Set.range a) ≃[L]
          Substructure.closure L (Set.range b),
        ∀ i, e ⟨a i, Substructure.subset_closure ⟨i, rfl⟩⟩ =
          ⟨b i, Substructure.subset_closure ⟨i, rfl⟩⟩ :=
  atomicEquivalent_iff_exists_closure_equiv a b

end

#assert_standard_axioms test_atomicEquivalent_refl
#assert_standard_axioms test_atomicEquivalent_symm
#assert_standard_axioms test_atomicEquivalent_trans
#assert_standard_axioms test_atomicEquivalent_iff_formulas
#assert_standard_axioms test_atomicEquivalent_iff_closure_equiv
