/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.Dovetail
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: the dovetailing scheduler

**The two halves are gated separately, and they rest on different facts.**
`test_fires_at_most_once` is the negative half: it follows from the monotone fired record and the
unfired guard, and `avail_mono` is not used in its proof. `test_valid_eventually_fires` is the
positive half — the load-bearing one, since "at most once" alone is satisfied by a schedule that
fires nothing — and it consumes *both* `avail_mono` and least-selection.

**The fixture exercises delay without starvation.** Requirement `3` is available from stage `0`,
while `0`, `1`, `2` become available at stages `1`, `2`, `3` in turn. So `3` is continuously
fireable from the very first stage and yet fires *last*, at stage `4`: it is delayed by exactly the
three smaller requirements and by nothing else.

That is what makes this fixture worth having. In an all-at-once fixture — everything available from
stage `0` — the schedule would fire `0, 1, 2, 3` in order and the fairness argument would never be
tested, because no requirement would ever be passed over while available. Here `3` is passed over
three times, and `test_three_delayed_not_starved` records both halves of that: passed over at
stages `0`–`3`, fired at `4`.

The row also pins the bounded-search convention: at stage `0` only code `0` is considered, so even
though `3` is available it cannot be selected — which is why the delay is finite rather than a
starvation.
-/

/-! ### The general theorems -/

/-- **At most once**, at an arbitrary availability datum. -/
theorem test_fires_at_most_once (A : DovetailAvail) {e s t : ℕ}
    (hs : A.FiresAt e s) (ht : A.FiresAt e t) : s = t :=
  A.fires_at_most_once hs ht

/-- **Eventually fires**, from availability at a single stage. -/
theorem test_valid_eventually_fires (A : DovetailAvail) {e s₀ : ℕ}
    (h : A.avail s₀ e = true) : ∃ s, A.FiresAt e s :=
  A.valid_eventually_fires h

/-- Least-selection, exposed: an available unfired index within the clock's range is never skipped
in favour of a larger one. This is the ingredient the positive half rests on. -/
theorem test_least_selection (A : DovetailAvail) {fired : List ℕ} {s e : ℕ} (hle : e ≤ s)
    (havail : A.avail s e = true) (hmem : e ∉ fired) :
    ∃ e', A.pick fired s = some e' ∧ e' ≤ e :=
  A.exists_pick_of_avail hle havail hmem

/-- The record only grows, and never repeats — the two facts the negative half rests on. -/
theorem test_record_monotone_nodup (A : DovetailAvail) {s t : ℕ} (h : s ≤ t) :
    A.fired s <+: A.fired t ∧ (A.fired t).Nodup :=
  ⟨A.fired_prefix h, A.fired_nodup t⟩

/-! ### The fixture: delayed, not starved -/

/-- Requirement `3` is available from the start; `0`, `1`, `2` become available at stages `1`, `2`,
`3`. Monotone in the stage, as required. -/
def delayedAvail : DovetailAvail where
  avail s e := decide (e = 3) || decide (e < 3 ∧ e + 1 ≤ s)
  avail_mono := by
    intro s t e hst h
    rcases Bool.or_eq_true_iff.mp h with h | h
    · simp [h]
    · simp only [decide_eq_true_eq] at h
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inr ⟨h.1, le_trans h.2 hst⟩

/-- **`3` is available at every stage**, including the first. -/
theorem test_three_available_immediately (s : ℕ) : delayedAvail.avail s 3 = true := by
  simp [delayedAvail]

/-- **Delayed, not starved.** Requirement `3` is passed over at stages `0`, `1`, `2`, `3` — at the
first because the clock's bounded search has not reached code `3`, at the others because a smaller
requirement has just become available — and fires at stage `4`. -/
theorem test_three_delayed_not_starved :
    (∀ s, s < 4 → ¬ delayedAvail.FiresAt 3 s) ∧ delayedAvail.FiresAt 3 4 := by
  refine ⟨?_, by decide⟩
  intro s hs
  rcases s with _ | _ | _ | _ | s
  · decide
  · decide
  · decide
  · decide
  · omega

/-- The smaller requirements fire in order, one per stage, each exactly when it becomes
available. -/
theorem test_smaller_fire_in_order :
    delayedAvail.FiresAt 0 1 ∧ delayedAvail.FiresAt 1 2 ∧ delayedAvail.FiresAt 2 3 := by
  refine ⟨by decide, by decide, by decide⟩

/-- Nothing fires at stage `0`: the bounded search considers only code `0`, which is not yet
available. This is what makes `3`'s delay finite rather than a starvation. -/
theorem test_nothing_fires_at_zero (e : ℕ) : ¬ delayedAvail.FiresAt e 0 := by
  have h : delayedAvail.pick (delayedAvail.fired 0) 0 = none := by decide
  intro hf
  rw [DovetailAvail.FiresAt, h] at hf
  exact absurd hf (by simp)

/-- The record after five stages, in firing order. -/
theorem test_record_after_five : delayedAvail.fired 5 = [0, 1, 2, 3] := by
  decide

#assert_standard_axioms test_fires_at_most_once
#assert_standard_axioms test_valid_eventually_fires
#assert_standard_axioms test_least_selection
#assert_standard_axioms test_record_monotone_nodup
#assert_standard_axioms test_three_available_immediately
#assert_standard_axioms test_three_delayed_not_starved
#assert_standard_axioms test_smaller_fire_in_order
#assert_standard_axioms test_nothing_fires_at_zero
#assert_standard_axioms test_record_after_five
