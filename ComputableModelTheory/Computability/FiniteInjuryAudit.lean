/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.FiniteInjury
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: the finite-injury kernel

**The row that matters most is a refutation.** `test_unguarded_breaks_locality` exhibits a concrete
state and action at which the *unguarded* truncation changes a position of strictly higher priority
than the actor. That is the failure `apply`'s guard exists to prevent, and it is recorded as a
theorem so that removing the guard cannot look like a simplification. `test_out_of_range_is_noop`
is the guard itself.

**Locality is gated before anything derived from it**, and `test_prefix_is_derived` records the
dependency rather than merely the fact: prefix preservation is a consequence of locality, not an
independent `take`/`append` computation, so the two cannot drift.

**`GoodState` is gated as a separate predicate.** `test_locality_needs_no_goodness` takes no
goodness hypothesis at all — it typechecks precisely because the kernel's primitive does not have
one — while `test_goodness_is_preserved` shows the predicate is nonetheless maintained, under the
single obligation the actor discharges. If goodness ever migrates into the state or into a kernel
hypothesis, the first of these rows stops meaning anything.

**The stabilization hypothesis is gated by shape.** `test_stabilization_hypothesis` states the
theorem with `LocallyFinite` written out, so the assumption is visible in the row: priority `e`
acts finitely often *given* that every higher priority does. There is no scheduling discipline, no
progress measure, no computable stabilization stage, and no bound on how often a priority acts. A
future proof that needs one of those is proving a different theorem.

**The toy run tests injury, not the induction.** Its schedule is eventually silent outright, so
`toy_locallyFinite` does not exercise the conditional structure of `LocallyFinite`; what it does
exercise is the truncation — a priority genuinely loses a value it held, and recovers with a
different one. Without it every theorem here would be consistent with a construction in which
nothing is ever overwritten.

Nothing in this tranche mentions `Partrec.race`, staged partial functions, or relative merge
machinery, and nothing should until there is a consumer.
-/

namespace FiniteInjury

/-! ### The guard, and the failure it prevents -/

/-- **The out-of-range no-op.** -/
theorem test_out_of_range_is_noop :
    StageState.apply (⟨[]⟩ : StageState ℕ) ⟨3, 7⟩ = ⟨[]⟩ :=
  rfl

/-- The unguarded truncation, defined here and nowhere else: it exists only to be refuted. -/
private def applyUnguarded {α : Type*} (s : StageState α) (act : Action α) : StageState α :=
  ⟨s.values.take act.prio ++ [act.value]⟩

/-- **Without the guard, injury locality is false.** At `prio = 3` on the empty state the
unguarded action installs at position `0` — a position of strictly *higher* priority than the
actor. Every downstream theorem rests on this not happening, so the counterexample is recorded
rather than described. -/
theorem test_unguarded_breaks_locality :
    ∃ (s : StageState ℕ) (act : Action ℕ) (i : ℕ),
      i < act.prio ∧ (applyUnguarded s act).values[i]? ≠ s.values[i]? :=
  ⟨⟨[]⟩, ⟨3, 7⟩, 0, by decide, by decide⟩

/-- And the guarded action agrees with the unguarded one exactly where the guard passes, so the
guard costs nothing in range. -/
theorem test_guard_is_free {α : Type*} (s : StageState α) (act : Action α)
    (h : act.prio ≤ s.values.length) :
    StageState.apply s act = applyUnguarded s act :=
  StageState.apply_of_le h

/-! ### Locality, and what is derived from it -/

/-- **Injury locality, the primitive.** Unconditional: no hypothesis on the state, and none on the
action beyond `apply`'s own guard. -/
theorem test_injury_locality {α : Type*} (s : StageState α) (act : Action α) {i : ℕ}
    (h : i < act.prio) : (StageState.apply s act).values[i]? = s.values[i]? :=
  StageState.apply_getElem?_of_lt s act h

/-- **Prefix preservation, and the record that it is derived.** Both statements are gated together
because the content is the dependency: the second follows from the first pointwise, so a refactor
that re-proves prefixes from `take`/`append` lemmas would leave them free to drift. -/
theorem test_prefix_is_derived {α : Type*} (s : StageState α) (act : Action α) {n : ℕ}
    (h : n ≤ act.prio) :
    (StageState.apply s act).values.take n = s.values.take n ∧
      ∀ i < act.prio, (StageState.apply s act).values[i]? = s.values[i]? :=
  ⟨StageState.take_apply_of_le s act h, fun _ hi ↦ StageState.apply_getElem?_of_lt s act hi⟩

/-! ### Goodness stays outside -/

/-- **The kernel's primitive takes no goodness hypothesis.** This row typechecks precisely because
`GoodState` is not a field of the state and not an assumption of locality; if it ever became
either, this statement would no longer be the general one. -/
theorem test_locality_needs_no_goodness {α : Type*} (s : StageState α) (act : Action α) {i : ℕ}
    (h : i < act.prio) : (StageState.apply s act).values[i]? = s.values[i]? :=
  StageState.apply_getElem?_of_lt s act h

/-- **Goodness is nonetheless preserved**, under exactly one obligation: the incoming value meets
its own priority's requirement. The surviving prefix is good by locality; the installed value
because the actor said so. -/
theorem test_goodness_is_preserved {α : Type*} {P : ℕ → α → Prop} {s : StageState α}
    {act : Action α} (hs : GoodState P s) (hact : P act.prio act.value) :
    GoodState P (StageState.apply s act) :=
  hs.apply hact

/-- The empty state is good for anything, so the predicate is never vacuously unavailable. -/
theorem test_goodness_starts : GoodState (fun (_ : ℕ) (_ : ℕ) ↦ True) ⟨[]⟩ :=
  goodState_nil _

/-! ### Stabilization -/

/-- **The stabilization hypothesis, written out.** Exactly the frozen local-finiteness assumption —
priority `e` acts finitely often *given* that every higher priority does — and nothing else: no
scheduling discipline, no progress measure, no computable stabilization stage, no bound on how
often a priority may act. -/
theorem test_stabilization_hypothesis {α : Type*} (init : StageState α)
    (sched : ℕ → Option (Action α))
    (h : ∀ e, (∀ i, i < e → EventuallySilent sched i) → EventuallySilent sched e) (e : ℕ) :
    ∃ N, ∀ n, N ≤ n → (run init sched n).values[e]? = (run init sched N).values[e]? :=
  stabilizes_of_localFinite h e

/-- The intermediate fact the induction actually runs on: from some stage, no priority `≤ e` acts
again. Assembled by induction rather than by a finite maximum, so the schedule's shape is never
consulted. -/
theorem test_silence_below {α : Type*} {sched : ℕ → Option (Action α)} (h : LocallyFinite sched)
    (e : ℕ) : ∃ N, ∀ n, N ≤ n → ∀ p, p ≤ e → ¬ ActsAt sched p n :=
  exists_silent_below h e

/-! ### The toy run: a genuine injury -/

/-- **A priority really is injured.** At stage `2` priority `1` holds `8`; priority `0` acts at
that stage; at stage `3` priority `1` holds nothing. Without this row the truncation in `apply`
would be untested. -/
theorem test_toy_injury :
    (toyRun 2).values[1]? = some 8 ∧ ActsAt toySched 0 2 ∧ (toyRun 3).values[1]? = none :=
  toy_injury

/-- **And the injury is not undone**: priority `1` recovers with a different value. -/
theorem test_toy_recovery : (toyRun 4).values[1]? = some 5 ∧ (toyRun 4) = ⟨[9, 5]⟩ :=
  ⟨toy_recovery, rfl⟩

/-- The run settles, injured priority included. -/
theorem test_toy_settles (e : ℕ) : Settles ⟨[]⟩ toySched e :=
  toy_settles e

/-- And it is constant from stage `4` on, so "settles" is not vacuous here. -/
theorem test_toy_constant {n : ℕ} (h : 4 ≤ n) : toyRun n = ⟨[9, 5]⟩ :=
  toyRun_eq_of_four_le h

/-! ### Local finiteness without global silence

The toy run is eventually silent outright, which leaves one thing untested: whether
`stabilizes_of_localFinite` is really about *each priority* settling, or whether it quietly relies
on the whole construction going quiet. The diagonal schedule separates the two — priority `e` acts
exactly once, at stage `e`, so every priority is eventually silent, while *some* priority acts at
every single stage and the state grows without bound. -/

/-- At stage `n`, priority `n` acts. Never silent, globally. -/
private def diagonalSched : ℕ → Option (Action ℕ) :=
  fun n ↦ some ⟨n, n⟩

private theorem diagonal_actsAt_iff {e n : ℕ} : ActsAt diagonalSched e n ↔ n = e := by
  constructor
  · rintro ⟨act, hact, rfl⟩
    exact (Option.some.inj hact) ▸ rfl
  · rintro rfl
    exact ⟨⟨n, n⟩, rfl, rfl⟩

/-- The state after `n` stages is `[0, 1, …, n-1]`: it never stops growing. -/
private theorem diagonal_run (n : ℕ) :
    run ⟨[]⟩ diagonalSched n = ⟨List.range n⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run_succ_some (rfl : diagonalSched n = some ⟨n, n⟩), ih,
      StageState.apply_of_le (by simp), List.range_succ]
    simp

/-- **Every priority is eventually silent** — each acts exactly once. -/
theorem test_diagonal_locallyFinite : LocallyFinite diagonalSched :=
  fun e _ ↦ ⟨e + 1, fun n hn hact ↦ by
    have := diagonal_actsAt_iff.1 hact
    omega⟩

/-- **But the schedule is never globally silent**: at every stage some priority acts, so no `N`
makes the whole construction quiet. This is what the toy run cannot show. -/
theorem test_diagonal_not_globally_silent :
    ¬ ∃ N, ∀ n, N ≤ n → ∀ e, ¬ ActsAt diagonalSched e n := by
  rintro ⟨N, hN⟩
  exact hN N (Nat.le_refl N) N (diagonal_actsAt_iff.2 rfl)

/-- **And the state grows without bound**, so stabilization here is genuinely per-position rather
than a statement about the state settling. -/
theorem test_diagonal_state_unbounded (n : ℕ) :
    (run ⟨[]⟩ diagonalSched n).values.length = n := by
  rw [diagonal_run]
  exact List.length_range

/-- **Yet every position settles.** Position `e` takes the value `e` at stage `e + 1` and never
moves again — stabilization under local finiteness alone, with the construction still running. -/
theorem test_diagonal_settles (e : ℕ) :
    Settles ⟨[]⟩ diagonalSched e ∧
      ∀ n, e < n → (run ⟨[]⟩ diagonalSched n).values[e]? = some e := by
  refine ⟨stabilizes_of_localFinite test_diagonal_locallyFinite e, fun n hn ↦ ?_⟩
  rw [diagonal_run]
  exact List.getElem?_range hn

end FiniteInjury

#assert_standard_axioms FiniteInjury.test_out_of_range_is_noop
#assert_standard_axioms FiniteInjury.test_unguarded_breaks_locality
#assert_standard_axioms FiniteInjury.test_guard_is_free
#assert_standard_axioms FiniteInjury.test_injury_locality
#assert_standard_axioms FiniteInjury.test_prefix_is_derived
#assert_standard_axioms FiniteInjury.test_locality_needs_no_goodness
#assert_standard_axioms FiniteInjury.test_goodness_is_preserved
#assert_standard_axioms FiniteInjury.test_goodness_starts
#assert_standard_axioms FiniteInjury.test_stabilization_hypothesis
#assert_standard_axioms FiniteInjury.test_silence_below
#assert_standard_axioms FiniteInjury.test_toy_injury
#assert_standard_axioms FiniteInjury.test_toy_recovery
#assert_standard_axioms FiniteInjury.test_toy_settles
#assert_standard_axioms FiniteInjury.test_toy_constant
#assert_standard_axioms FiniteInjury.test_diagonal_locallyFinite
#assert_standard_axioms FiniteInjury.test_diagonal_not_globally_silent
#assert_standard_axioms FiniteInjury.test_diagonal_state_unbounded
#assert_standard_axioms FiniteInjury.test_diagonal_settles
