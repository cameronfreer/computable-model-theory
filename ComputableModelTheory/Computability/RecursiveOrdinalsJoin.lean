/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.OracleJoin
import ComputableModelTheory.Computability.RecursiveOrdinals

/-!
# The join bound for `ω₁^X`

The one consequence of the oracle join for recursive ordinals that is automatic: since the join
computes both components, both boundaries are at most the join's. **Equality with the maximum is
not asserted**, and nothing here supports it.
-/

namespace omegaOneOf

/-- **The automatic join bound**, by monotonicity through the two projections. -/
theorem max_le_join (X Y : ℕ →. ℕ) :
    max (omegaOneOf X) (omegaOneOf Y) ≤ omegaOneOf (join X Y) :=
  max_le (mono (join.recursiveIn_left X Y)) (mono (join.recursiveIn_right X Y))

end omegaOneOf
