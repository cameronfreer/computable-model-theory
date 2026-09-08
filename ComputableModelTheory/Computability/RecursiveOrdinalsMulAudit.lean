/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.SetTheory.Ordinal.Principal
import ComputableModelTheory.Computability.RecursiveOrdinalsMul
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: `ω · β` from a presentation of `β`

**The order of multiplication is checked, not trusted.** From the presentation of `2`, the
construction yields type `ω · 2 = ω + ω` (`test_two_copies`), which differs from `2 · ω = ω`
(`test_not_the_other_order`). The ordering itself is inspected: every element of copy `0` lies
below every element of copy `1` (`test_copy_zero_below_copy_one`), and within a copy the order is
`<` on the second coordinate (`test_within_copy`).

**The boundary consequence.** `test_omega0_mul_lt` is `β < ω₁^X → ω · β < ω₁^X`, from
representability alone.
-/

open Encodable Ordinal RecWellOrder

variable (X : ℕ →. ℕ)

/-- **Two copies of `ω`**: type `ω · 2 = ω + ω`. -/
theorem test_two_copies : (finOrder X 2).mulOmega.type = ω * 2 ∧ ω * 2 = ω + ω := by
  refine ⟨?_, Ordinal.mul_two ω⟩
  rw [type_mulOmega, type_finOrder, Nat.cast_ofNat]

/-- **Not the other order**: `2 · ω = ω`, which is strictly below `ω · 2`. -/
theorem test_not_the_other_order : (2 : Ordinal) * ω = ω ∧ ω < ω * 2 := by
  refine ⟨?_, ?_⟩
  · exact_mod_cast natCast_mul_omega0 (n := 2) two_pos
  · rw [Ordinal.mul_two]
    exact lt_add_of_pos_right ω omega0_pos

/-- **Copy `0` lies entirely below copy `1`**: `(0, 1000)` precedes `(1, 0)`, and not conversely. -/
theorem test_copy_zero_below_copy_one :
    (finOrder X 2).mulOmega.rel (Nat.pair 0 1000) (Nat.pair 1 0) ∧
      ¬ (finOrder X 2).mulOmega.rel (Nat.pair 1 0) (Nat.pair 0 1000) := by
  constructor
  · exact Or.inl (by simp [finOrder, Nat.unpair_pair])
  · rintro (h | ⟨h, -⟩)
    · simp [finOrder, Nat.unpair_pair] at h
    · simp [Nat.unpair_pair] at h

/-- **Within a copy** the order is `<` on the second coordinate. -/
theorem test_within_copy :
    (finOrder X 2).mulOmega.rel (Nat.pair 1 3) (Nat.pair 1 7) ∧
      ¬ (finOrder X 2).mulOmega.rel (Nat.pair 1 7) (Nat.pair 1 3) := by
  constructor
  · exact Or.inr (by simp [Nat.unpair_pair])
  · rintro (h | ⟨-, h⟩)
    · simp [finOrder, Nat.unpair_pair] at h
    · simp [Nat.unpair_pair] at h

/-- Both coordinates of a domain element are recovered; a first coordinate outside the base domain
is excluded. -/
theorem test_domain :
    Nat.pair 1 5 ∈ (finOrder X 2).mulOmega.domain ∧
      Nat.pair 2 5 ∉ (finOrder X 2).mulOmega.domain := by
  constructor
  · show (Nat.unpair (Nat.pair 1 5)).1 < 2
    rw [Nat.unpair_pair]; decide
  · show ¬ (Nat.unpair (Nat.pair 2 5)).1 < 2
    rw [Nat.unpair_pair]; decide

/-- **The boundary consequence.** -/
theorem test_omega0_mul_lt (β : Ordinal.{0}) (h : β < omegaOneOf X) : ω * β < omegaOneOf X :=
  omegaOneOf.omega0_mul_lt h

#assert_standard_axioms test_two_copies
#assert_standard_axioms test_not_the_other_order
#assert_standard_axioms test_copy_zero_below_copy_one
#assert_standard_axioms test_within_copy
#assert_standard_axioms test_domain
#assert_standard_axioms test_omega0_mul_lt
