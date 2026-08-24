/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.StagedPartial
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: staged partial computations

The layer is **supplied data**, and the rows are chosen so that this stays visible.

`test_supplied_not_derived` builds a `StagedPartialIn` from explicit approximation data and nothing
else — no `RecursiveIn` hypothesis appears anywhere in this file. There is deliberately no theorem
`RecursiveIn O f → StagedPartialIn O f`; that is a relativized oracle-machine representation
theorem with its own content, and the absence cannot be gated directly, so what is gated instead is
that the API is inhabited and usable *without* it.

**The fixture stages non-trivially, on purpose.** `stagedRange` discovers `x` only from stage
`x + 1` on, so the discovery stage grows with the input and cannot be read off a fixed stage. A
constant approximation would satisfy every law below while testing nothing about staging, and would
make the racing consumer's problem invisible.

`test_stage_is_not_determined` is the row the next tranche depends on: two staged approximations of
the *same* function can discover the same value at different stages. So a consumer that inspects a
current stage is choosing between presentations, not between functions — which is why the racing
layer has to fix a discovery rule rather than read a current-stage value.
-/

open Encodable

namespace StagedPartialIn

/-! ### Supplied data, with a stage that actually matters -/

/-- The identity on `ℕ`, discovered at stage `x + 1` and not before. -/
def stagedRange (O : Set (ℕ →. ℕ)) : StagedPartialIn O (fun x : ℕ ↦ Part.some x) where
  approx s x := if x < s then some x else none
  approx_computableIn := by
    have h : ComputableIn O fun p : ℕ × ℕ ↦ decide (p.2 < p.1) :=
      (Primrec.nat_lt.decide.to_comp.computableIn₂ (O := O)).comp
        ComputableIn.snd ComputableIn.fst
    refine (ComputableIn.cond h (ComputableIn.option_some.comp ComputableIn.snd)
      (ComputableIn.const none)).of_eq fun p ↦ ?_
    by_cases hp : p.2 < p.1 <;> simp [hp]
  sound := by
    intro s x y h
    by_cases hx : x < s
    · rw [if_pos hx] at h
      rw [← Option.some.inj h]
      exact Part.mem_some _
    · rw [if_neg hx] at h
      exact absurd h (by simp)
  monotone := by
    intro s t x y hst h
    by_cases hx : x < s
    · rw [if_pos hx] at h
      rw [if_pos (Nat.lt_of_lt_of_le hx hst)]
      exact h
    · rw [if_neg hx] at h
      exact absurd h (by simp)
  complete := by
    intro x y h
    rw [Part.mem_some_iff] at h
    subst h
    exact ⟨y + 1, by simp⟩

/-- **The layer is inhabited from supplied data alone.** No `RecursiveIn` hypothesis appears in
this file; the representation theorem that would produce staged data from extensional
computability is a separate obligation and is deliberately absent. -/
theorem test_supplied_not_derived (O : Set (ℕ →. ℕ)) :
    Nonempty (StagedPartialIn O (fun x : ℕ ↦ Part.some x)) :=
  ⟨stagedRange O⟩

/-- **The stage genuinely matters**: `x` is invisible at every stage `≤ x`, and visible from
`x + 1` on. A constant approximation would pass every other row here while testing nothing. -/
theorem test_stage_matters (O : Set (ℕ →. ℕ)) (x : ℕ) :
    (stagedRange O).approx x x = none ∧ (stagedRange O).approx (x + 1) x = some x :=
  ⟨by simp [stagedRange], by simp [stagedRange]⟩

/-! ### The extensional API -/

/-- **Membership is discovery.** -/
theorem test_mem_iff_exists_approx {α β : Type*} [Primcodable α] [Primcodable β]
    {O : Set (ℕ →. ℕ)} {f : α →. β} (F : StagedPartialIn O f) {x : α} {y : β} :
    y ∈ f x ↔ ∃ s, F.approx s x = some y :=
  F.mem_iff_exists_approx

/-- **Halting is discovery of something.** -/
theorem test_dom_iff_exists_approx {α β : Type*} [Primcodable α] [Primcodable β]
    {O : Set (ℕ →. ℕ)} {f : α →. β} (F : StagedPartialIn O f) {x : α} :
    (f x).Dom ↔ ∃ s y, F.approx s x = some y :=
  F.dom_iff_exists_approx

/-- **Persistence**, and that a discovery is the only one: the two facts a consumer needs before it
may treat "found by stage `s`" as stable information. -/
theorem test_persistence {α β : Type*} [Primcodable α] [Primcodable β]
    {O : Set (ℕ →. ℕ)} {f : α →. β} (F : StagedPartialIn O f) {s t : ℕ} {x : α} {y z : β}
    (h : s ≤ t) (hs : F.approx s x = some y) (ht : F.approx t x = some z) :
    F.approx t x = some y ∧ y = z :=
  ⟨F.approx_of_le h hs, F.approx_unique hs ht⟩

/-- Nothing is ever discovered off the domain. -/
theorem test_nothing_off_domain {α β : Type*} [Primcodable α] [Primcodable β]
    {O : Set (ℕ →. ℕ)} {f : α →. β} (F : StagedPartialIn O f) {x : α}
    (h : ¬ (f x).Dom) (s : ℕ) : F.approx s x = none :=
  F.approx_eq_none_of_not_dom h s

/-! ### What the approximation does *not* determine -/

/-- A second staged approximation of the same function, discovering everything at stage `0`. -/
def stagedNow (O : Set (ℕ →. ℕ)) : StagedPartialIn O (fun x : ℕ ↦ Part.some x) where
  approx _ x := some x
  approx_computableIn := ComputableIn.option_some.comp ComputableIn.snd
  sound := by
    intro s x y h
    rw [← Option.some.inj h]
    exact Part.mem_some _
  monotone := by
    intro s t x y _ h
    exact h
  complete := by
    intro x y h
    rw [Part.mem_some_iff] at h
    exact ⟨0, by rw [h]⟩

/-- **The stage is not determined by the function.** Two staged approximations of the *same*
partial function disagree about when a value is found — here at every positive input, at stage `0`.

This is the row the racing tranche rests on: a consumer that reads a current-stage value is
choosing between *presentations*, not between functions, so a race must fix a discovery rule rather
than inspect a fixed stage. -/
theorem test_stage_is_not_determined (O : Set (ℕ →. ℕ)) :
    (stagedNow O).approx 0 1 = some 1 ∧ (stagedRange O).approx 0 1 = none :=
  ⟨rfl, by simp [stagedRange]⟩

end StagedPartialIn

#assert_standard_axioms StagedPartialIn.test_supplied_not_derived
#assert_standard_axioms StagedPartialIn.test_stage_matters
#assert_standard_axioms StagedPartialIn.test_mem_iff_exists_approx
#assert_standard_axioms StagedPartialIn.test_dom_iff_exists_approx
#assert_standard_axioms StagedPartialIn.test_persistence
#assert_standard_axioms StagedPartialIn.test_nothing_off_domain
#assert_standard_axioms StagedPartialIn.test_stage_is_not_determined
