/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.RecursiveOrdinalsJoin
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: the join bound

**Only the maximum inequality.** `test_max_le_join` is the automatic bound; there is no row
asserting equality with the maximum, because none is proved.
-/

/-- **The maximum inequality**, and nothing more. -/
theorem test_max_le_join (X Y : ℕ →. ℕ) :
    max (omegaOneOf X) (omegaOneOf Y) ≤ omegaOneOf (join X Y) :=
  omegaOneOf.max_le_join X Y

#assert_standard_axioms test_max_le_join
