/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.AgeChainWitness
import ComputableModelTheory.ModelTheory.Computable.PartialAge
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: uniform witness extraction

Two fixtures, chosen so the search is exercised rather than assumed:

* an all-`ℕ` family, where the identity enumeration produces a value at step `0` — the degenerate
  case, which would make every row below pass even if `firstSomeStep` returned `0` outright;
* a family whose enumeration is silent until step `3`, which pins that it really is the **least
  step with a value** and not the least step, the least value, or a constant.

The second fixture is the one that matters: `firstSomeStep` returns a *step* index, and its value
`5` is unrelated to it, so a confusion between steps and carrier elements cannot survive both rows.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

section

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-! ### The degenerate case -/

private theorem allNat_nonempty (K : ComputableAgeIn O L) (n : ℕ) :
    (K.toPartialAge.domainAt (id n)).Nonempty :=
  ⟨0, 0, rfl⟩

/-- An all-`ℕ` family enumerates a value at step `0` — the case that would hide a `firstSomeStep`
which ignored its argument. -/
theorem test_firstSomeStep_allNat (K : ComputableAgeIn O L) (n : ℕ) :
    K.toPartialAge.firstSomeStep id (allNat_nonempty K) n = 0 := by
  rw [PartialAgeIn.firstSomeStep, Nat.find_eq_zero]
  rfl

end

section

variable {O : Set (ℕ →. ℕ)}

/-! ### A family that is silent until step 3 -/

/-- Over a language with no function symbols every term is a variable. -/
private theorem empty_term_eq_var {n : ℕ} (v : Fin n → ℕ)
    (T : Language.empty.Term (Fin n)) :
    ∃ k, @Term.realize Language.empty ℕ _ _ v T = v k := by
  induction T with
  | var k => exact ⟨k, rfl⟩
  | func f _ _ => exact isEmptyElim f

/-- Every member records the single generator `5` and enumerates nothing before step `3`. -/
noncomputable def lateAge : PartialAgeIn O Language.empty where
  structureAt _ := inferInstance
  enum? _ m := if m = 3 then Option.some 5 else Option.none
  enum?_computableIn := by
    have h : Primrec fun p : ℕ × ℕ ↦ if p.2 = 3 then Option.some 5 else Option.none :=
      Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 3))
        (Primrec.const (Option.some 5)) (Primrec.const Option.none)
    exact h.to_comp.computableIn
  gens _ := [5]
  gens_computableIn := ComputableIn.const _
  funEval _ _ := Part.none
  funEval_recursiveIn := RecursiveIn.none
  funEval_correct := fun _ d _ ↦ isEmptyElim d
  relEval _ _ := Part.none
  relEval_recursiveIn := RecursiveIn.none
  relEval_correct := fun _ d _ ↦ isEmptyElim d
  generates := fun _ x ↦ by
    have hx : (∃ m, (if m = 3 then Option.some 5 else Option.none) = Option.some x) ↔ x = 5 := by
      constructor
      · rintro ⟨m, hm⟩
        by_cases h : m = 3
        · rw [h, if_pos rfl] at hm
          exact (Option.some_inj.1 hm).symm
        · rw [if_neg h] at hm
          exact absurd hm (by simp)
      · rintro rfl
        exact ⟨3, by rw [if_pos rfl]⟩
    rw [hx]
    constructor
    · rintro rfl
      exact ⟨Term.var ⟨0, by simp⟩, rfl⟩
    · rintro ⟨T, rfl⟩
      obtain ⟨k, hk⟩ := empty_term_eq_var (Tuple.view ([5] : Tuple ℕ)) T
      rw [hk]
      exact match k with
        | ⟨0, _⟩ => rfl
        | ⟨_ + 1, h⟩ => absurd h (by simp)

private theorem lateAge_enum?_three (i : ℕ) :
    (lateAge (O := O)).enum? i 3 = Option.some 5 := by
  show (if (3 : ℕ) = 3 then Option.some 5 else Option.none) = Option.some 5
  rw [if_pos rfl]

private theorem lateAge_enum?_of_ne {i m : ℕ} (h : m ≠ 3) :
    (lateAge (O := O)).enum? i m = Option.none := by
  show (if m = 3 then Option.some 5 else Option.none) = Option.none
  rw [if_neg h]

private theorem lateAge_nonempty (n : ℕ) :
    ((lateAge (O := O)).domainAt (id n)).Nonempty :=
  ⟨5, 3, lateAge_enum?_three _⟩

/-- **The search really searches.** The first step with a value is `3`. -/
theorem test_firstSomeStep_eq_three (n : ℕ) :
    (lateAge (O := O)).firstSomeStep id lateAge_nonempty n = 3 := by
  rw [PartialAgeIn.firstSomeStep, Nat.find_eq_iff]
  refine ⟨by rw [lateAge_enum?_three]; rfl, fun m hm ↦ ?_⟩
  rw [lateAge_enum?_of_ne (by omega : m ≠ 3)]
  simp

/-- **And the value is not the step.** `firstSomeStep` is `3`; the witness it extracts is `5`. -/
theorem test_firstEnumeratedValue_eq_five (n : ℕ) :
    (lateAge (O := O)).firstEnumeratedValue id lateAge_nonempty n = 5 := by
  have h := (lateAge (O := O)).enum?_firstSomeStep id lateAge_nonempty n
  rw [test_firstSomeStep_eq_three, lateAge_enum?_three] at h
  exact (Option.some_inj.1 h).symm

/-- The witness equation, at the fixture: exactly the input `toCePresentation` consumes. -/
theorem test_enum?_firstSomeStep (n : ℕ) :
    (lateAge (O := O)).enum? (id n)
        ((lateAge (O := O)).firstSomeStep id lateAge_nonempty n) =
      Option.some ((lateAge (O := O)).firstEnumeratedValue id lateAge_nonempty n) :=
  (lateAge (O := O)).enum?_firstSomeStep id lateAge_nonempty n

/-- The extracted witness is a carrier element. -/
theorem test_firstEnumeratedValue_mem (n : ℕ) :
    (lateAge (O := O)).firstEnumeratedValue id lateAge_nonempty n ∈
      (lateAge (O := O)).domainAt (id n) :=
  (lateAge (O := O)).firstEnumeratedValue_mem id lateAge_nonempty n

/-- Both extractions are computable, uniformly in the schedule. -/
theorem test_witness_computableIn :
    ComputableIn O ((lateAge (O := O)).firstSomeStep id lateAge_nonempty) ∧
      ComputableIn O ((lateAge (O := O)).firstEnumeratedValue id lateAge_nonempty) :=
  ⟨(lateAge (O := O)).firstSomeStep_computableIn id lateAge_nonempty ComputableIn.id,
    (lateAge (O := O)).firstEnumeratedValue_computableIn id lateAge_nonempty ComputableIn.id⟩

end

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.test_firstSomeStep_allNat
#assert_standard_axioms FirstOrder.Language.test_firstSomeStep_eq_three
#assert_standard_axioms FirstOrder.Language.test_firstEnumeratedValue_eq_five
#assert_standard_axioms FirstOrder.Language.test_enum?_firstSomeStep
#assert_standard_axioms FirstOrder.Language.test_firstEnumeratedValue_mem
#assert_standard_axioms FirstOrder.Language.test_witness_computableIn
