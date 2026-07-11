/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.TupleClosure
import ComputableModelTheory.ModelTheory.Computable.SuccExample
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for tuples and semantic tuple closure

Named acceptance tests for the tuple API and the central closure gate, checked by
`#assert_standard_axioms`. Outside the root import spine; CI checks it explicitly with

```
lake env lean ComputableModelTheory/ModelTheory/TupleClosureAudit.lean
```
-/

open FirstOrder Language

section

variable {L : Language} {M N : Type*} [L.Structure M] [L.Structure N] {k : ℕ}

/-- The central semantic gate: closure membership is term realization. -/
theorem test_mem_closure_range_iff (a : Fin k → M) (x : M) :
    x ∈ Substructure.closure L (Set.range a) ↔
      ∃ t : L.Term (Fin k), t.realize a = x :=
  mem_closure_range_iff_exists_term a

/-- The list form of the gate through the fixed-width view. -/
theorem test_tuple_mem_closure_iff (a : Tuple M) (x : M) :
    x ∈ Tuple.closure L a ↔ ∃ t : L.Term (Fin a.length), t.realize a.view = x :=
  Tuple.mem_closure_iff_exists_term a

/-- Generation is every element being a term value. -/
theorem test_generates_iff (a : Fin k → M) :
    Generates L a ↔ ∀ x : M, ∃ t : L.Term (Fin k), t.realize a = x :=
  generates_iff a

/-- Covering the entries of a tuple yields closure containment. -/
theorem test_closure_range_mono {m : ℕ} (a : Fin k → M) (b : Fin m → M)
    (h : ∀ i, ∃ j, b j = a i) :
    Substructure.closure L (Set.range a) ≤ Substructure.closure L (Set.range b) :=
  closure_range_mono h

/-- A homomorphism maps a tuple closure onto the image tuple's closure. -/
theorem test_map_closure_range (f : M →[L] N) (a : Fin k → M) :
    (Substructure.closure L (Set.range a)).map f =
      Substructure.closure L (Set.range (f ∘ a)) :=
  map_closure_range f a

end

section ConcreteClosure

attribute [local instance] succStructure

/-- The singleton tuple `0` generates the successor structure on `ℕ`: every natural
number is an iterated-successor term value. -/
theorem test_succ_generates : Generates succLang (M := ℕ) ![0] := by
  rw [generates_iff]
  intro x
  induction x with
  | zero => exact ⟨Term.var 0, rfl⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨Term.func SuccFunctions.succ ![t], ?_⟩
    rw [Term.realize_func]
    show (![t] 0).realize ![0] + 1 = n + 1
    rw [Matrix.cons_val_zero, ht]

/-- A concrete closure membership through the gate: `2` lies in the closure of the
tuple `0` in the successor structure. -/
theorem test_succ_closure_mem :
    (2 : ℕ) ∈ Substructure.closure succLang (Set.range ![(0 : ℕ)]) :=
  (mem_closure_range_iff_exists_term _).2
    ⟨Term.func SuccFunctions.succ ![Term.func SuccFunctions.succ ![Term.var 0] ], rfl⟩

end ConcreteClosure

#assert_standard_axioms test_mem_closure_range_iff
#assert_standard_axioms test_tuple_mem_closure_iff
#assert_standard_axioms test_generates_iff
#assert_standard_axioms test_closure_range_mono
#assert_standard_axioms test_map_closure_range
#assert_standard_axioms test_succ_generates
#assert_standard_axioms test_succ_closure_mem
