/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.OracleJoin
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: the join of two oracles

**Interleaving, on partial oracles.** `test_even_odd` reads both components back through the join
on concrete inputs. `test_partial_preserved` joins the everywhere-undefined oracle with a total one
and checks that the undefined half stays undefined while the total half is read — nothing is
totalized by joining.

**The universal property is gated in both directions.** `test_projections` are the two reductions
at the join itself; `test_universal` is the full iff at an arbitrary oracle set.

The ordinal consequence of the join is audited with the ordinal layer
(`RecursiveOrdinalsJoinAudit`), not here: this module depends only on the computability substrate.
-/

open Encodable

/-- The identity and the doubling oracle. -/
def idOracle : ℕ →. ℕ := fun n ↦ Part.some n
def dblOracle : ℕ →. ℕ := fun n ↦ Part.some (2 * n)

/-- **Both components read back**: `join id dbl 6 = id 3 = 3`, `join id dbl 7 = dbl 3 = 6`. -/
theorem test_even_odd : join idOracle dblOracle 6 = Part.some 3 ∧
    join idOracle dblOracle 7 = Part.some 6 := by
  refine ⟨?_, ?_⟩
  · have := join.two_mul idOracle dblOracle 3
    simpa [idOracle] using this
  · have := join.two_mul_add_one idOracle dblOracle 3
    simpa [dblOracle] using this

/-- **Partiality is preserved**: the undefined half stays undefined, the total half is read. -/
theorem test_partial_preserved (n : ℕ) :
    ¬ (join (fun _ ↦ Part.none) idOracle (2 * n)).Dom ∧
      (join (fun _ ↦ Part.none) idOracle (2 * n + 1)) = Part.some n := by
  refine ⟨?_, ?_⟩
  · rw [join.two_mul]; exact fun h ↦ h
  · rw [join.two_mul_add_one]; rfl

/-- **The two projections**, at the join itself. -/
theorem test_projections (X Y : ℕ →. ℕ) :
    RecursiveIn {join X Y} X ∧ RecursiveIn {join X Y} Y :=
  ⟨join.recursiveIn_left X Y, join.recursiveIn_right X Y⟩

/-- **The universal reduction property.** -/
theorem test_universal (X Y : ℕ →. ℕ) (O : Set (ℕ →. ℕ)) :
    RecursiveIn O (join X Y) ↔ RecursiveIn O X ∧ RecursiveIn O Y :=
  join.recursiveIn_join_iff X Y

/-- A consequence in the transport vocabulary: the join computes anything either component does. -/
theorem test_join_computes_components (X Y : ℕ →. ℕ) {f : ℕ →. ℕ}
    (h : RecursiveIn {X} f) : RecursiveIn {join X Y} f :=
  RecursiveIn.subst h fun _ hg ↦ by
    rw [Set.mem_singleton_iff] at hg; rw [hg]; exact join.recursiveIn_left X Y

#assert_standard_axioms test_even_odd
#assert_standard_axioms test_partial_preserved
#assert_standard_axioms test_projections
#assert_standard_axioms test_universal
#assert_standard_axioms test_join_computes_components
