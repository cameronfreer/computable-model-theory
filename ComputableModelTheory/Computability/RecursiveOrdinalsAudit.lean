/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Order.OrderIsoNat
import ComputableModelTheory.Computability.RecursiveOrdinals
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: ordinals recursive in one oracle

**The concrete presentations compute the right types.** Empty, singleton, a larger finite order,
`ω`, and `ω + 1` — the last as the successor of the `ω` presentation, which is exactly the case
where the original domain is all of `ℕ` and no unused natural number can be assumed.

**Restriction has the computed type.** `test_restrict_finOrder` restricts the presentation of `5`
below its element `3` and reads off type `3`.

**A domain whose membership uses the oracle.** `test_oracle_domain` presents the even numbers under
`<` relative to the total characteristic oracle of `Even`, through the existing self-computability
theorem for that oracle; its type is `ω`, through the order isomorphism of an infinite decidable
subset of `ℕ` with `ℕ`.

**Monotonicity is an actual transport**, not a statement-only test: `test_transport_composes`
transports a presentation along a reduction and reads back the same domain, relation, and type; and
`test_equiv_invariance` composes the two directions of a Turing equivalence.

**The boundary.** `test_boundary_not_presented`, `test_strict_cut_on_examples` (`ω` and `5` are
below the boundary because they are presented; the boundary itself is not, so it is not below
itself), `test_below_omega_one`, and `test_no_greatest`.
-/

open Encodable Ordinal Cardinal RecWellOrder

variable (X : ℕ →. ℕ)

/-! ### Concrete presentations -/

theorem test_empty : (emptyOrder X).type = 0 := type_emptyOrder X

theorem test_singleton : (finOrder X 1).type = 1 := by rw [type_finOrder, Nat.cast_one]

theorem test_five : (finOrder X 5).type = 5 := by rw [type_finOrder, Nat.cast_ofNat]

theorem test_omega : (natOrder X).type = ω := type_natOrder X

/-- **`ω + 1`**, as the successor of the presentation on all of `ℕ`. -/
theorem test_omega_succ : (natOrder X).succ.type = ω + 1 := by
  rw [type_succ, type_natOrder]

/-- The successor of the presentation on all of `ℕ` really moved everything: `0` is its new top, so
the old `0` now sits at `1`, and `0` is not below anything. -/
theorem test_succ_shift : (natOrder X).succ.rel 1 0 ∧ ¬ (natOrder X).succ.rel 0 1 := by
  refine ⟨Or.inr ⟨Nat.one_pos, rfl⟩, ?_⟩
  rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact lt_irrefl _ h

/-- **Restriction below an element has the computed type**: `5` restricted below `3` is `3`. -/
theorem test_restrict_finOrder : ((finOrder X 5).restrict 3).type = 3 := by
  have h3 : (3 : ℕ) ∈ (finOrder X 5).domain := (by omega : (3 : ℕ) < 5)
  rw [type_restrict _ h3, ← type_subrel,
    show (3 : Ordinal) = ((3 : ℕ) : Ordinal) from Nat.cast_ofNat.symm, ← type_fin 3]
  -- the initial segment below `3` in `{n | n < 5}` under `<` is order-isomorphic to `Fin 3`
  exact RelIso.ordinalType_congr
    ⟨{ toFun := fun x ↦ ⟨x.1.1, x.2⟩
       invFun := fun i ↦ ⟨⟨i.1, lt_trans i.2 (by decide)⟩, i.2⟩
       left_inv := fun _ ↦ rfl
       right_inv := fun _ ↦ rfl }, Iff.rfl⟩

/-! ### A domain whose membership uses the oracle -/

/-- The even numbers under `<`, presented relative to the total characteristic oracle of `Even`. -/
def evenOrder : RecWellOrder (predOracleTotal (fun n : ℕ ↦ Even n)) where
  domain := {n | Even n}
  domain_computable :=
    (computablePredIn_predOracleTotal_self (fun n : ℕ ↦ Even n)).of_eq fun _ ↦ Iff.rfl
  rel := (· < ·)
  rel_computable := ComputableIn.computablePredIn (Primrec.nat_lt.decide.to_comp.computableIn)
  isWellOrder := inferInstance

instance : Infinite ({n : ℕ | Even n} : Set ℕ) :=
  Infinite.of_injective (fun k : ℕ ↦ (⟨2 * k, even_two_mul k⟩ : ({n : ℕ | Even n} : Set ℕ)))
    fun _ _ h ↦ by simpa using congrArg Subtype.val h

/-- **The oracle-dependent domain has type `ω`.** -/
theorem test_oracle_domain : evenOrder.type = ω := by
  rw [← type_nat_lt]
  exact (RelIso.ordinalType_congr
    (Nat.Subtype.orderIsoOfNat {n : ℕ | Even n}).toRelIsoLT).symm

/-! ### Transport -/

/-- **Transport composes**: along an actual reduction, the domain, relation, and type come back
unchanged. -/
theorem test_transport_composes {Y : ℕ →. ℕ} (h : RecursiveIn {Y} X) (W : RecWellOrder X) :
    (W.transport h).domain = W.domain ∧ (W.transport h).rel = W.rel ∧
      (W.transport h).type = W.type :=
  ⟨rfl, rfl, rfl⟩

/-- Presented ordinals transport, and the boundary is monotone. -/
theorem test_mono {Y : ℕ →. ℕ} (h : RecursiveIn {Y} X) :
    RecOrdinals X ⊆ RecOrdinals Y ∧ omegaOneOf X ≤ omegaOneOf Y :=
  ⟨RecOrdinals.mono h, omegaOneOf.mono h⟩

/-- **Turing-equivalence invariance**, from the two directions. -/
theorem test_equiv_invariance {Y : ℕ →. ℕ} (hXY : RecursiveIn {Y} X) (hYX : RecursiveIn {X} Y) :
    omegaOneOf X = omegaOneOf Y :=
  omegaOneOf.eq_of_equiv hXY hYX

/-- Transport along the trivial reduction of an oracle to itself is the identity on types. -/
theorem test_transport_self (W : RecWellOrder X) :
    (W.transport (RecursiveIn.iff_nat.2 (Nat.RecursiveIn.oracle X rfl))).type = W.type := rfl

/-! ### The boundary -/

theorem test_countable : (RecOrdinals X).Countable := RecOrdinals.countable

theorem test_boundary_not_presented : omegaOneOf X ∉ RecOrdinals X :=
  omegaOneOf.notMem_recOrdinals

/-- **The strict cut on examples**: `ω` and `5` are below the boundary because they are presented;
the boundary is not below itself. -/
theorem test_strict_cut_on_examples :
    ω < omegaOneOf X ∧ (5 : Ordinal) < omegaOneOf X ∧ ¬ omegaOneOf X < omegaOneOf X :=
  ⟨omegaOneOf.lt_iff.2 RecOrdinals.omega0_mem,
    omegaOneOf.lt_iff.2 (by simpa using RecOrdinals.natCast_mem (X := X) 5),
    fun h ↦ omegaOneOf.notMem_recOrdinals (omegaOneOf.lt_iff.1 h)⟩

theorem test_strict_cut : ∀ α : Ordinal.{0}, α < omegaOneOf X ↔ α ∈ RecOrdinals X :=
  fun _ ↦ omegaOneOf.lt_iff

theorem test_below_omega_one : omegaOneOf X < ω_ 1 := omegaOneOf.lt_omega_one

/-- **No greatest presented ordinal.** -/
theorem test_no_greatest : ∀ α, α < omegaOneOf X → α + 1 < omegaOneOf X :=
  fun _ ↦ omegaOneOf.succ_lt

#assert_standard_axioms test_empty
#assert_standard_axioms test_singleton
#assert_standard_axioms test_five
#assert_standard_axioms test_omega
#assert_standard_axioms test_omega_succ
#assert_standard_axioms test_succ_shift
#assert_standard_axioms test_restrict_finOrder
#assert_standard_axioms test_oracle_domain
#assert_standard_axioms test_transport_composes
#assert_standard_axioms test_mono
#assert_standard_axioms test_equiv_invariance
#assert_standard_axioms test_transport_self
#assert_standard_axioms test_countable
#assert_standard_axioms test_boundary_not_presented
#assert_standard_axioms test_strict_cut_on_examples
#assert_standard_axioms test_strict_cut
#assert_standard_axioms test_below_omega_one
#assert_standard_axioms test_no_greatest
