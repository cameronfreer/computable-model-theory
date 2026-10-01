/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.FiniteElimination
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: finite elimination

Three concrete traces, each discharging all four hypotheses.

* **Non-monotone, with silent stages** (`oneZero`). Candidate `1` is selected at stage `1`, and
  refuted from stage `3` on. Candidate `0` is selected at stage `3`. Every other stage is silent.
  The selection *decreases*, so no monotone-pointer argument applies, yet the trace is
  non-repeating, has at most `B + 1 = 2` selections, and is silent from stage `4`.
* **The bound attained** (`descending`). Candidates `2, 1, 0` are selected at stages `1, 2, 3`,
  each refuted by the next selection: exactly `B + 1 = 3` selections. The count is tight.
* **One selection, then permanent silence** (`single`). Candidate `5` is selected at stage `0` and
  never refuted. Every later stage is silent, and the selection stages are exactly `{0}`.
-/

open FiniteElimination

namespace FiniteEliminationAudit

/-! ### `1`, then `0`, with silent stages -/

/-- Select `1` at stage `1` and `0` at stage `3`; every other stage is silent. -/
def oneZeroSel (t : ℕ) : Option ℕ :=
  if t = 1 then some 1 else if t = 3 then some 0 else none

/-- Candidate `1` is refuted from stage `3` on; nothing else is ever refuted. -/
def oneZeroRef (s c : ℕ) : Prop :=
  c = 1 ∧ 3 ≤ s

theorem oneZero_persistent : Persistent oneZeroRef := fun _ _ _ hst ⟨hc, hs⟩ ↦ ⟨hc, by omega⟩

theorem oneZero_rejects : RejectsRefuted oneZeroRef oneZeroSel := by
  intro t c h ⟨hc, hs⟩
  unfold oneZeroSel at h
  split_ifs at h with h1 h3 <;> simp at h <;> omega

theorem oneZero_replaces : ReplacesRefuted oneZeroRef oneZeroSel := by
  intro t t' c hc htt' ht' hbetween
  unfold oneZeroSel at hc ht'
  split_ifs at hc with h1 h3
  · -- the selection of `1` at stage `1`: the next selection is at stage `3`
    have hc1 : c = 1 := by simpa using hc.symm
    split_ifs at ht' with h1' h3'
    · omega
    · exact ⟨hc1, by omega⟩
    · simp at ht'
  · -- the selection of `0` at stage `3`: there is no later selection
    split_ifs at ht' with h1' h3' <;> first | omega | simp at ht'

theorem oneZero_bounded : EventuallyBounded oneZeroSel 0 1 := by
  intro t c _ h
  unfold oneZeroSel at h
  split_ifs at h <;> simp at h <;> omega

/-- **Non-monotone**: the later selection is the *smaller* candidate. -/
theorem test_oneZero_nonmonotone : oneZeroSel 1 = some 1 ∧ oneZeroSel 3 = some 0 :=
  ⟨rfl, rfl⟩

/-- **Non-repetition, the count, and eventual silence** — all from the general theorems. -/
theorem test_oneZero :
    (selectionStagesFrom oneZeroSel 0).ncard ≤ 2 ∧ ∃ M, ∀ t, M ≤ t → oneZeroSel t = none :=
  ⟨ncard_selectionStagesFrom_le oneZero_persistent oneZero_rejects oneZero_replaces
      oneZero_bounded,
    eventually_none oneZero_persistent oneZero_rejects oneZero_replaces oneZero_bounded⟩

/-- Silent stages are genuinely present between the two selections. -/
theorem test_oneZero_silent : oneZeroSel 0 = none ∧ oneZeroSel 2 = none ∧ ∀ t, 4 ≤ t →
    oneZeroSel t = none := by
  refine ⟨rfl, rfl, fun t ht ↦ ?_⟩
  unfold oneZeroSel
  split_ifs <;> first | rfl | omega

/-! ### The bound attained -/

/-- Select `2, 1, 0` at stages `1, 2, 3`. -/
def descSel (t : ℕ) : Option ℕ :=
  if t = 1 then some 2 else if t = 2 then some 1 else if t = 3 then some 0 else none

/-- Each candidate is refuted from the next selection stage on. -/
def descRef (s c : ℕ) : Prop :=
  (c = 2 ∧ 2 ≤ s) ∨ (c = 1 ∧ 3 ≤ s)

theorem desc_persistent : Persistent descRef := by
  rintro s t c hst (⟨hc, hs⟩ | ⟨hc, hs⟩)
  · exact Or.inl ⟨hc, by omega⟩
  · exact Or.inr ⟨hc, by omega⟩

theorem desc_rejects : RejectsRefuted descRef descSel := by
  intro t c h hr
  unfold descSel at h
  split_ifs at h <;> simp at h <;> rcases hr with ⟨hc, hs⟩ | ⟨hc, hs⟩ <;> omega

theorem desc_replaces : ReplacesRefuted descRef descSel := by
  intro t t' c hc htt' ht' hbetween
  unfold descSel at hc ht'
  split_ifs at hc with h1 h2 h3
  · -- `2` at stage `1`; the next selection is at stage `2`
    have hc2 : c = 2 := by simpa using hc.symm
    split_ifs at ht' with h1' h2' h3'
    · omega
    · exact Or.inl ⟨hc2, by omega⟩
    · exact Or.inl ⟨hc2, by omega⟩
    · simp at ht'
  · -- `1` at stage `2`; the next selection is at stage `3`
    have hc1 : c = 1 := by simpa using hc.symm
    split_ifs at ht' with h1' h2' h3'
    · omega
    · omega
    · exact Or.inr ⟨hc1, by omega⟩
    · simp at ht'
  · -- `0` at stage `3`; there is no later selection
    split_ifs at ht' with h1' h2' h3' <;> first | omega | simp at ht'

theorem desc_bounded : EventuallyBounded descSel 0 2 := by
  intro t c _ h
  unfold descSel at h
  split_ifs at h <;> simp at h <;> omega

/-- **The bound is attained**: exactly `B + 1 = 3` selections. The general theorem gives `≤ 3`, and
the three stages `1, 2, 3` give `≥ 3`. -/
theorem test_desc_attains_bound : (selectionStagesFrom descSel 0).ncard = 3 := by
  have hle := ncard_selectionStagesFrom_le desc_persistent desc_rejects desc_replaces desc_bounded
  have hsub : ({1, 2, 3} : Set ℕ) ⊆ selectionStagesFrom descSel 0 := by
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    refine ⟨Nat.zero_le _, ?_⟩
    rcases ht with rfl | rfl | rfl <;> rfl
  have h3 : ({1, 2, 3} : Set ℕ).ncard = 3 := by
    rw [Set.ncard_eq_three]
    exact ⟨1, 2, 3, by decide, by decide, by decide, rfl⟩
  have hge := Set.ncard_le_ncard hsub
    (finite_selectionStagesFrom desc_persistent desc_rejects desc_replaces desc_bounded)
  omega

/-! ### One selection, then permanent silence -/

/-- Select `5` at stage `0`; silent forever after. -/
def singleSel (t : ℕ) : Option ℕ :=
  if t = 0 then some 5 else none

/-- Nothing is ever refuted. -/
def neverRef (_ _ : ℕ) : Prop :=
  False

theorem single_persistent : Persistent neverRef := fun _ _ _ _ h ↦ h

theorem single_rejects : RejectsRefuted neverRef singleSel := fun _ _ _ h ↦ h

theorem single_replaces : ReplacesRefuted neverRef singleSel := by
  intro t t' c hc htt' ht' _
  unfold singleSel at hc ht'
  split_ifs at hc ht' <;> first | omega | simp at ht'

theorem single_bounded : EventuallyBounded singleSel 0 5 := by
  intro t c _ h
  unfold singleSel at h
  split_ifs at h
  simp only [Option.some.injEq] at h
  omega

/-- **A single selection, then permanent silence**: the selection stages are exactly `{0}`, and
every later stage is silent. -/
theorem test_single :
    selectionStagesFrom singleSel 0 = {0} ∧ ∀ t, 1 ≤ t → singleSel t = none := by
  refine ⟨Set.ext fun t ↦ ?_, fun t ht ↦ ?_⟩
  · simp only [selectionStagesFrom, singleSel, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, h⟩
      by_contra hne
      simp [hne] at h
    · rintro rfl
      exact ⟨le_rfl, rfl⟩
  · unfold singleSel
    split_ifs <;> first | rfl | omega

/-- The general theorems apply to it too. -/
theorem test_single_general :
    (selectionStagesFrom singleSel 0).ncard ≤ 6 ∧ ∃ M, ∀ t, M ≤ t → singleSel t = none :=
  ⟨ncard_selectionStagesFrom_le single_persistent single_rejects single_replaces single_bounded,
    eventually_none single_persistent single_rejects single_replaces single_bounded⟩

end FiniteEliminationAudit

#assert_standard_axioms FiniteEliminationAudit.test_oneZero_nonmonotone
#assert_standard_axioms FiniteEliminationAudit.test_oneZero
#assert_standard_axioms FiniteEliminationAudit.test_oneZero_silent
#assert_standard_axioms FiniteEliminationAudit.test_desc_attains_bound
#assert_standard_axioms FiniteEliminationAudit.test_single
#assert_standard_axioms FiniteEliminationAudit.test_single_general

#assert_module_standard_axioms ComputableModelTheory.Computability.FiniteElimination
