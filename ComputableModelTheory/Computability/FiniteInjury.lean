/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.List.Basic

/-!
# The finite-injury kernel

The combinatorial core of a finite-injury priority construction, isolated from everything that
will eventually sit on top of it. There is **no computability here at all** — no `RecursiveIn`, no
staged partial functions, no racing — and that is the point: stabilization is a statement about a
sequence of finite states, and mixing it with effectivity would make it look as though it needed
an oracle.

## The state and the action

A `StageState` is a list of held values, indexed by priority, with **smaller index = higher
priority**. It is deliberately **proof-free**: no invariant is bundled, so the kernel's theorems
cannot silently depend on one. Anything a particular construction wants to maintain is a separate
predicate — see `GoodState`.

An `Action` is a priority together with the value to install there. Acting is **truncating**:
everything at strictly lower priority is discarded, which is exactly what "injury" means.

## The guard is load-bearing

`apply` is guarded by `act.prio ≤ s.values.length`, and out of range it is a **no-op**. Without
the guard, `take e ++ [a]` at `e > length` appends at position `length` rather than at `e` — so a
*lower*-priority action would change a *higher*-priority position, and `apply_getElem?_of_lt`
below would be **false**. The guard is what makes injury locality hold unconditionally, and hence
what lets `GoodState` stay a separate predicate instead of becoming a hypothesis of every kernel
theorem. `FiniteInjuryAudit` exhibits the failure explicitly rather than describing it.

## The order of proof

`apply_getElem?_of_lt` — injury locality — is the **primitive**. Prefix preservation
(`take_apply_of_le`) is *derived* from it pointwise through `List.ext_getElem?`, never proved
independently from `take`/`append` lemmas: derived, the two cannot drift apart.

## What stabilization actually assumes

`stabilizes_of_localFinite` takes exactly one hypothesis: **priority `e` acts finitely often given
that every higher priority does**. No scheduling hypothesis, no progress measure, no computable
stabilization stage, and no assumption that a priority acts at most once. The induction needs
nothing else, and if a future extension seems to want more, that is a signal the statement has
drifted rather than a licence to strengthen the hypothesis.
-/

namespace FiniteInjury

variable {α : Type*}

/-! ### States and actions -/

/-- The state of a priority construction at one stage: the values currently held, indexed by
priority, with **smaller index = higher priority**.

Proof-free by design — no invariant is bundled, so no kernel theorem can depend on one. -/
structure StageState (α : Type*) where
  /-- The held values, in priority order. -/
  values : List α

@[ext] theorem StageState.ext {s t : StageState α} (h : s.values = t.values) : s = t := by
  cases s; cases t; simpa using h

/-- An action: install `value` at priority `prio`, discarding everything of strictly lower
priority. The truncation *is* the injury. -/
structure Action (α : Type*) where
  /-- The acting priority. -/
  prio : ℕ
  /-- The value to install there. -/
  value : α

namespace StageState

/-- **Acting, guarded.** In range, truncate to the acting priority and install; out of range, do
nothing.

The guard is not defensive tidiness. Unguarded, an action at `prio > values.length` would install
at position `values.length`, changing a position of *higher* priority than the actor — and
`apply_getElem?_of_lt` would fail. -/
def apply (s : StageState α) (act : Action α) : StageState α :=
  if act.prio ≤ s.values.length then ⟨s.values.take act.prio ++ [act.value]⟩ else s

@[simp] theorem apply_of_le {s : StageState α} {act : Action α}
    (h : act.prio ≤ s.values.length) :
    s.apply act = ⟨s.values.take act.prio ++ [act.value]⟩ :=
  if_pos h

/-- **The out-of-range no-op.** -/
@[simp] theorem apply_of_gt {s : StageState α} {act : Action α}
    (h : s.values.length < act.prio) : s.apply act = s :=
  if_neg (Nat.not_le.2 h)

/-! ### Injury locality — the primitive theorem -/

/-- **Injury locality.** An action at priority `e` leaves every strictly higher priority
untouched.

This is the kernel's primitive, and it holds *unconditionally* — no hypothesis on the state, and
none on the action beyond what `apply`'s own guard supplies. Everything else about the state is
derived from it. -/
theorem apply_getElem?_of_lt (s : StageState α) (act : Action α) {i : ℕ} (h : i < act.prio) :
    (s.apply act).values[i]? = s.values[i]? := by
  rcases Nat.lt_or_ge s.values.length act.prio with hgt | hle
  · rw [apply_of_gt hgt]
  · rw [apply_of_le hle]
    have hlen : (s.values.take act.prio).length = act.prio := by
      rw [List.length_take]
      exact Nat.min_eq_left hle
    rw [List.getElem?_append_left (by rw [hlen]; exact h), List.getElem?_take]
    exact if_pos h

/-- **Prefix preservation, derived.** Every prefix up to the acting priority survives.

Proved pointwise from `apply_getElem?_of_lt` through `List.ext_getElem?` — deliberately *not*
from `take`/`append` lemmas independently, so that locality and prefix preservation cannot drift
apart under refactoring. -/
theorem take_apply_of_le (s : StageState α) (act : Action α) {n : ℕ} (h : n ≤ act.prio) :
    (s.apply act).values.take n = s.values.take n := by
  refine List.ext_getElem? fun i ↦ ?_
  rw [List.getElem?_take, List.getElem?_take]
  by_cases hi : i < n
  · rw [if_pos hi, if_pos hi]
    exact apply_getElem?_of_lt s act (Nat.lt_of_lt_of_le hi h)
  · rw [if_neg hi, if_neg hi]

end StageState

/-! ### Goodness, as a separate predicate

What a particular construction maintains about its state is *not* part of the state and *not* a
hypothesis of the kernel. It is a predicate, preserved by `apply` under exactly the obligation the
actor discharges: the incoming value meets its own priority's requirement. -/

/-- A state is good for a per-priority requirement when every held value meets the requirement of
the priority holding it. Stated on `getElem?`, so no bound has to be threaded. -/
def GoodState (P : ℕ → α → Prop) (s : StageState α) : Prop :=
  ∀ i a, s.values[i]? = some a → P i a

/-- The empty state is good for any requirement. -/
theorem goodState_nil (P : ℕ → α → Prop) : GoodState P ⟨[]⟩ := by
  intro i a h
  simp at h

/-- **Goodness is preserved by acting**, given only that the acting value meets the acting
priority's requirement. The surviving prefix is good because it was — that is injury locality
again — and the installed value because the actor said so. -/
theorem GoodState.apply {P : ℕ → α → Prop} {s : StageState α} {act : Action α}
    (hs : GoodState P s) (hact : P act.prio act.value) : GoodState P (s.apply act) := by
  rcases Nat.lt_or_ge s.values.length act.prio with hgt | hle
  · rwa [StageState.apply_of_gt hgt]
  intro i a hia
  rcases Nat.lt_or_ge i act.prio with hlt | hge
  · exact hs i a ((StageState.apply_getElem?_of_lt s act hlt) ▸ hia)
  have hlen : (s.values.take act.prio).length = act.prio := by
    rw [List.length_take]; exact Nat.min_eq_left hle
  rw [StageState.apply_of_le hle] at hia
  rw [List.getElem?_append_right (by omega), hlen] at hia
  rcases Nat.eq_or_lt_of_le hge with heq | hgt'
  · rw [← heq, Nat.sub_self] at hia
    rw [← heq, ← Option.some.inj hia]
    exact hact
  · rw [show i - act.prio = (i - act.prio - 1) + 1 from by omega] at hia
    simp at hia

/-! ### Runs

A run is an initial state together with a schedule saying which action, if any, fires at each
stage. Nothing here assumes a priority acts at most once, or that the schedule is computable, or
that stages are related to anything else. -/

/-- The state after `n` stages of a schedule. -/
def run (init : StageState α) (sched : ℕ → Option (Action α)) : ℕ → StageState α
  | 0 => init
  | n + 1 =>
    match sched n with
    | none => run init sched n
    | some act => (run init sched n).apply act

@[simp] theorem run_zero (init : StageState α) (sched : ℕ → Option (Action α)) :
    run init sched 0 = init :=
  rfl

@[simp] theorem run_succ_none {init : StageState α} {sched : ℕ → Option (Action α)} {n : ℕ}
    (h : sched n = none) : run init sched (n + 1) = run init sched n := by
  rw [run, h]

@[simp] theorem run_succ_some {init : StageState α} {sched : ℕ → Option (Action α)} {n : ℕ}
    {act : Action α} (h : sched n = some act) :
    run init sched (n + 1) = (run init sched n).apply act := by
  rw [run, h]

/-- Priority `e` acts at stage `n`. -/
def ActsAt (sched : ℕ → Option (Action α)) (e n : ℕ) : Prop :=
  ∃ act, sched n = some act ∧ act.prio = e

/-- Priority `e` acts only finitely often: from some stage on, never. -/
def EventuallySilent (sched : ℕ → Option (Action α)) (e : ℕ) : Prop :=
  ∃ N, ∀ n, N ≤ n → ¬ ActsAt sched e n

/-- **The frozen local-finiteness assumption**, and the only hypothesis stabilization takes:
priority `e` acts finitely often **given** that every higher priority does.

Nothing stronger is assumed anywhere below — no scheduling discipline, no progress measure, no
computable stabilization stage, and no bound on how often a priority may act. -/
def LocallyFinite (sched : ℕ → Option (Action α)) : Prop :=
  ∀ e, (∀ i, i < e → EventuallySilent sched i) → EventuallySilent sched e

/-- Position `e` never changes from stage `N` on. -/
def SettledFrom (init : StageState α) (sched : ℕ → Option (Action α)) (e N : ℕ) : Prop :=
  ∀ n, N ≤ n → (run init sched n).values[e]? = (run init sched N).values[e]?

/-- Position `e` eventually stops changing. -/
def Settles (init : StageState α) (sched : ℕ → Option (Action α)) (e : ℕ) : Prop :=
  ∃ N, SettledFrom init sched e N

/-! ### Stabilization -/

/-- Local finiteness makes every priority eventually silent, by strong induction. -/
theorem eventuallySilent_of_localFinite {sched : ℕ → Option (Action α)}
    (h : LocallyFinite sched) (e : ℕ) : EventuallySilent sched e := by
  induction e using Nat.strongRecOn with
  | _ e ih => exact h e fun i hi ↦ ih i hi

/-- From some stage on, **no** priority `≤ e` ever acts. Assembled by induction rather than by a
finite maximum, so nothing about the schedule's shape is needed. -/
theorem exists_silent_below {sched : ℕ → Option (Action α)} (h : LocallyFinite sched) :
    ∀ e, ∃ N, ∀ n, N ≤ n → ∀ p, p ≤ e → ¬ ActsAt sched p n := by
  intro e
  induction e with
  | zero =>
    obtain ⟨N, hN⟩ := eventuallySilent_of_localFinite h 0
    exact ⟨N, fun n hn p hp ↦ Nat.le_zero.1 hp ▸ hN n hn⟩
  | succ e ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨M, hM⟩ := eventuallySilent_of_localFinite h (e + 1)
    refine ⟨max N M, fun n hn p hp ↦ ?_⟩
    rcases Nat.lt_or_ge p (e + 1) with hlt | hge
    · exact hN n (Nat.le_trans (Nat.le_max_left _ _) hn) p (Nat.lt_succ_iff.1 hlt)
    · exact Nat.le_antisymm hp hge ▸ hM n (Nat.le_trans (Nat.le_max_right _ _) hn)

/-- A stretch of stages in which only priorities `> e` act leaves position `e` alone — injury
locality, propagated along the run. -/
theorem settledFrom_of_silent_below {init : StageState α} {sched : ℕ → Option (Action α)}
    {e N : ℕ} (h : ∀ n, N ≤ n → ∀ p, p ≤ e → ¬ ActsAt sched p n) :
    SettledFrom init sched e N := by
  have key : ∀ k, (run init sched (N + k)).values[e]? = (run init sched N).values[e]? := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [show N + (k + 1) = (N + k) + 1 from by omega]
      rcases hact : sched (N + k) with - | act
      · rw [run_succ_none hact]; exact ih
      · rw [run_succ_some hact, ← ih]
        refine StageState.apply_getElem?_of_lt _ act ?_
        by_contra hle
        exact h (N + k) (by omega) act.prio (Nat.not_lt.1 hle) ⟨act, hact, rfl⟩
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact key k

/-- **Stabilization.** Under local finiteness alone, every position of the run eventually stops
changing.

The hypothesis is exactly the frozen one. If a strengthening ever looks necessary — a schedule
discipline, a progress measure, a computable stabilization stage — the statement being proved has
drifted; the induction here needs none of them. -/
theorem stabilizes_of_localFinite {init : StageState α} {sched : ℕ → Option (Action α)}
    (h : LocallyFinite sched) (e : ℕ) : Settles init sched e := by
  obtain ⟨N, hN⟩ := exists_silent_below h e
  exact ⟨N, settledFrom_of_silent_below hN⟩

/-! ### A run with a genuine injury

The smallest run in which a priority is actually injured: priority `1` installs a value, priority
`0` then acts and destroys it, and priority `1` installs a different one. Without this, every
theorem above would be consistent with a construction in which nothing is ever overwritten, and the
truncation in `apply` would be untested.

The schedule is eventually silent outright, so it exercises *injury*, not the conditional structure
of `LocallyFinite`; the induction in `stabilizes_of_localFinite` is what carries that, and it is
tested by the statement rather than by this fixture. -/

/-- Priority `0` acts at stages `0` and `2`; priority `1` at stages `1` and `3`. -/
def toySched : ℕ → Option (Action ℕ)
  | 0 => some ⟨0, 7⟩
  | 1 => some ⟨1, 8⟩
  | 2 => some ⟨0, 9⟩
  | 3 => some ⟨1, 5⟩
  | _ + 4 => none

/-- The run of `toySched` from the empty state. -/
def toyRun : ℕ → StageState ℕ :=
  run ⟨[]⟩ toySched

theorem toySched_none : ∀ {n : ℕ}, 4 ≤ n → toySched n = none
  | 0, h => absurd h (by omega)
  | 1, h => absurd h (by omega)
  | 2, h => absurd h (by omega)
  | 3, h => absurd h (by omega)
  | _ + 4, _ => rfl

@[simp] theorem toyRun_two : toyRun 2 = ⟨[7, 8]⟩ := rfl

@[simp] theorem toyRun_three : toyRun 3 = ⟨[9]⟩ := rfl

@[simp] theorem toyRun_four : toyRun 4 = ⟨[9, 5]⟩ := rfl

/-- **A genuine injury.** Priority `1` holds `8` at stage `2`; priority `0` acts at stage `2`, and
at stage `3` priority `1` holds nothing at all. -/
theorem toy_injury :
    (toyRun 2).values[1]? = some 8 ∧ ActsAt toySched 0 2 ∧ (toyRun 3).values[1]? = none :=
  ⟨rfl, ⟨⟨0, 9⟩, rfl, rfl⟩, rfl⟩

/-- Priority `1` recovers with a *different* value, so the injury is not undone. -/
theorem toy_recovery : (toyRun 4).values[1]? = some 5 :=
  rfl

/-- The run is constant from stage `4` on. -/
theorem toyRun_eq_of_four_le {n : ℕ} (h : 4 ≤ n) : toyRun n = ⟨[9, 5]⟩ := by
  have key : ∀ k, toyRun (4 + k) = ⟨[9, 5]⟩ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [show 4 + (k + 1) = (4 + k) + 1 from by omega, toyRun,
        run_succ_none (toySched_none (by omega))]
      exact ih
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact key k

theorem toy_locallyFinite : LocallyFinite toySched := by
  refine fun e _ ↦ ⟨4, fun n hn hact ↦ ?_⟩
  obtain ⟨act, hs, -⟩ := hact
  rw [toySched_none hn] at hs
  exact absurd hs (by simp)

/-- Every priority of the toy run settles — including the injured one. -/
theorem toy_settles (e : ℕ) : Settles ⟨[]⟩ toySched e :=
  stabilizes_of_localFinite toy_locallyFinite e

end FiniteInjury
