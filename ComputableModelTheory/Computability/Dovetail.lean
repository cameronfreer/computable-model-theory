/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.NodupEquivFin

/-!
# A dovetailing scheduler

The scheduling substrate for an *effective dovetailing* construction: at each clock stage, fire the
**least** available requirement that has not fired yet. Nothing is injured, retracted or
recomputed — the record of what has fired only grows — so this is deliberately **not** the
finite-injury kernel, and does not import it.

## Proof-free, effectivity-free, and outside the model-theoretic namespaces

At the **root** namespace, like `StagedPartialIn`: nothing here depends on a language or on model
theory, and the fairness argument needs only Boolean availability and its monotonicity. When the
model-theoretic consumer arrives, computability of the schedule should be added under an explicit
hypothesis that `avail` is uniformly `ComputableIn E` — not built into this structure.

The state is a list of fired indices and nothing else, and `avail` is supplied `Bool`-valued data
with one law (monotonicity in the stage). No structure, language, presentation or oracle appears
here: the availability of a requirement in the intended application is
`(approx s e).isSome` together with the construction's own guards, but this module does not know
that.

## The two theorems, and what each rests on

* `fires_at_most_once` rests on the **monotone fired list and the unfired guard**, and on nothing
  else. Persistence of availability is not used, and would be the wrong thing to cite: a fired index
  is recorded, the record only grows, and selection skips anything recorded.
* `valid_eventually_fires` is where monotonicity of `avail` does its work, together with
  **least-selection** (`exists_pick_of_avail`): once `e` is available it stays available, the step
  always takes the least available unfired index, so only indices `< e` can precede it — finitely
  many, each at most once.

The second consumes the first, so the two are not independent; but they rest on different facts, and
`DovetailAudit` keeps them apart.

## Selection is bounded

At stage `s` only codes `≤ s` are considered, so each step is a bounded search: no unbounded search
for "the next successful event", and no progress hypothesis anywhere. A requirement that is
available but larger than the clock simply waits, which is what makes the delay in
`DovetailAudit`'s fixture finite rather than a starvation.
-/

/-- Supplied availability data: whether requirement `e` is available at stage `s`, monotone in the
stage. In the intended application this is a staged approximation's `isSome` conjoined with the
construction's fireability guards; nothing here depends on that reading. -/
structure DovetailAvail where
  /-- Requirement `e` is available at stage `s`. -/
  avail : ℕ → ℕ → Bool
  /-- Availability persists. -/
  avail_mono : ∀ {s t e : ℕ}, s ≤ t → avail s e = true → avail t e = true

namespace DovetailAvail

variable (A : DovetailAvail)

/-! ### The scheduler -/

/-- **Least-selection, bounded.** The least code `≤ s` that is available at `s` and has not fired.
`List.find?` over `List.range (s + 1)` is what makes "least" a definition rather than a side
condition. -/
def pick (fired : List ℕ) (s : ℕ) : Option ℕ :=
  (List.range (s + 1)).find? fun e ↦ A.avail s e && !fired.contains e

/-- The record of what has fired **before** stage `s`. Grows by at most one entry per stage and
never loses one. -/
def fired (A : DovetailAvail) : ℕ → List ℕ
  | 0 => []
  | s + 1 =>
    match A.pick (A.fired s) s with
    | some e => A.fired s ++ [e]
    | none => A.fired s

@[simp] theorem fired_zero : A.fired 0 = [] := rfl

/-- Requirement `e` fires at stage `s`. -/
def FiresAt (e s : ℕ) : Prop := A.pick (A.fired s) s = some e

/-- Firing is decidable — the schedule is data, so small runs can be checked by evaluation. -/
instance (e s : ℕ) : Decidable (A.FiresAt e s) :=
  decidable_of_iff (A.pick (A.fired s) s = some e) Iff.rfl

/-! ### What selection guarantees -/

theorem avail_of_pick {fired : List ℕ} {s e : ℕ} (h : A.pick fired s = some e) :
    A.avail s e = true :=
  ((Bool.and_eq_true _ _).mp (List.find?_eq_some_iff_getElem.mp h).1).1

theorem not_mem_of_pick {fired : List ℕ} {s e : ℕ} (h : A.pick fired s = some e) :
    e ∉ fired := by
  have hb := ((Bool.and_eq_true _ _).mp (List.find?_eq_some_iff_getElem.mp h).1).2
  simpa using hb

/-- **Selection really is least**: nothing available and unfired is skipped. Read off
`find?`'s index characterization, where `(List.range n)[j] = j`. -/
theorem not_avail_of_lt_pick {fired : List ℕ} {s e e' : ℕ} (h : A.pick fired s = some e')
    (hlt : e < e') : A.avail s e = false ∨ e ∈ fired := by
  obtain ⟨-, i, hi, hval, hbefore⟩ := List.find?_eq_some_iff_getElem.mp h
  have hival : i = e' := by simpa using hval
  subst hival
  have he : e < (List.range (s + 1)).length := by
    simp only [List.length_range] at hi ⊢
    omega
  have hj := hbefore e hlt
  rw [Bool.not_eq_true', Bool.and_eq_false_iff] at hj
  have hget : (List.range (s + 1))[e] = e := by simp
  rw [hget] at hj
  rcases hj with hj | hj
  · exact Or.inl hj
  · exact Or.inr (by simpa using hj)

/-- Something is always selected when an available unfired index is within the clock's range. -/
theorem exists_pick_of_avail {fired : List ℕ} {s e : ℕ} (hle : e ≤ s)
    (havail : A.avail s e = true) (hmem : e ∉ fired) :
    ∃ e', A.pick fired s = some e' ∧ e' ≤ e := by
  have hmatch : (A.avail s e && !fired.contains e) = true := by simp [havail, hmem]
  rcases hp : A.pick fired s with - | e'
  · exact absurd hmatch (by
      have := List.find?_eq_none.mp hp e (List.mem_range.2 (by omega))
      simpa using this)
  · refine ⟨e', rfl, ?_⟩
    by_contra hgt
    rcases A.not_avail_of_lt_pick (e := e) hp (by omega) with h | h
    · rw [h] at havail; exact absurd havail (by simp)
    · exact hmem h

/-! ### The fired record grows and never repeats -/

theorem fired_succ_of_some {s e : ℕ} (h : A.FiresAt e s) :
    A.fired (s + 1) = A.fired s ++ [e] := by
  rw [fired, h]

theorem fired_succ_of_none {s : ℕ} (h : A.pick (A.fired s) s = none) :
    A.fired (s + 1) = A.fired s := by
  rw [fired, h]

theorem fired_prefix_succ (s : ℕ) : A.fired s <+: A.fired (s + 1) := by
  rcases hp : A.pick (A.fired s) s with - | e
  · rw [A.fired_succ_of_none hp]
  · rw [A.fired_succ_of_some hp]
    exact List.prefix_append _ _

theorem fired_prefix {s t : ℕ} (h : s ≤ t) : A.fired s <+: A.fired t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => exact List.prefix_refl _
  | succ k ih => exact ih.trans (A.fired_prefix_succ (s + k))

theorem mem_fired_of_le {s t e : ℕ} (h : s ≤ t) (hmem : e ∈ A.fired s) : e ∈ A.fired t :=
  (A.fired_prefix h).subset hmem

theorem mem_fired_of_firesAt {e s : ℕ} (h : A.FiresAt e s) : e ∈ A.fired (s + 1) := by
  rw [A.fired_succ_of_some h]
  exact List.mem_append_right _ (by simp)

theorem fired_nodup (s : ℕ) : (A.fired s).Nodup := by
  induction s with
  | zero => simp
  | succ s ih =>
    rcases hp : A.pick (A.fired s) s with - | e
    · rw [A.fired_succ_of_none hp]; exact ih
    · rw [A.fired_succ_of_some hp]
      refine List.Nodup.append ih (List.nodup_singleton e) ?_
      intro a ha hb
      rw [List.mem_singleton] at hb
      exact A.not_mem_of_pick hp (hb ▸ ha)

/-! ### The two theorems -/

/-- **At most once.** A requirement fires at no more than one stage.

This uses only that the fired record grows (`fired_prefix`) and that selection skips what is
recorded (`not_mem_of_pick`). Monotonicity of `avail` is *not* used. -/
theorem fires_at_most_once {e s t : ℕ} (hs : A.FiresAt e s) (ht : A.FiresAt e t) : s = t := by
  by_contra hne
  rcases Nat.lt_or_ge s t with hlt | hge
  · exact absurd (A.mem_fired_of_le (by omega) (A.mem_fired_of_firesAt hs))
      (A.not_mem_of_pick ht)
  · have hlt : t < s := by omega
    exact absurd (A.mem_fired_of_le (by omega) (A.mem_fired_of_firesAt ht))
      (A.not_mem_of_pick hs)

/-- Every entry of the record fired at some stage — so the record is exactly the set of fired
requirements, and counting it counts firings. -/
theorem exists_firesAt_of_mem_fired {e : ℕ} :
    ∀ {s}, e ∈ A.fired s → ∃ n, n < s ∧ A.FiresAt e n := by
  intro s
  induction s with
  | zero => simp
  | succ s ih =>
    intro hmem
    rcases hp : A.pick (A.fired s) s with - | e'
    · rw [A.fired_succ_of_none hp] at hmem
      obtain ⟨n, hn, hfire⟩ := ih hmem
      exact ⟨n, by omega, hfire⟩
    · rw [A.fired_succ_of_some hp] at hmem
      rcases List.mem_append.1 hmem with h | h
      · obtain ⟨n, hn, hfire⟩ := ih h
        exact ⟨n, by omega, hfire⟩
      · rcases List.mem_singleton.1 h with rfl
        exact ⟨s, by omega, hp⟩

/-- **Eventually fires.** A requirement that ever becomes available fires at some stage.

Both ingredients are visible: `avail_mono` keeps `e` available while earlier requirements are
processed, and `exists_pick_of_avail` — least-selection — confines what can precede it to the
finitely many indices below `e`, each of which fires at most once. -/
theorem valid_eventually_fires {e s₀ : ℕ} (h : A.avail s₀ e = true) :
    ∃ s, A.FiresAt e s := by
  by_contra hnone
  simp only [not_exists] at hnone
  -- `e` never enters the record
  have hnotmem : ∀ s, e ∉ A.fired s := by
    intro s hmem
    obtain ⟨n, -, hfire⟩ := A.exists_firesAt_of_mem_fired hmem
    exact hnone n hfire
  set N := max s₀ e with hN
  have hs0 : s₀ ≤ N := le_max_left _ _
  have hes : e ≤ N := le_max_right _ _
  -- past `N`, every stage fires some index strictly below `e`
  have hstep : ∀ s, N ≤ s → ∃ e', A.FiresAt e' s ∧ e' < e := by
    intro s hs
    obtain ⟨e', hpick, hle⟩ :=
      A.exists_pick_of_avail (fired := A.fired s) (s := s) (e := e) (by omega)
        (A.avail_mono (by omega) h) (hnotmem s)
    refine ⟨e', hpick, ?_⟩
    rcases Nat.lt_or_ge e' e with hlt | hge
    · exact hlt
    · exact absurd (show e' = e by omega) (fun heq ↦ hnone s (heq ▸ hpick))
  -- so the record's entries below `e` grow by one per stage, yet there are at most `e` of them
  have hcount : ∀ m, m ≤ ((A.fired (N + m)).filter fun x ↦ decide (x < e)).length := by
    intro m
    induction m with
    | zero => omega
    | succ m ih =>
      obtain ⟨e', hfire, hlt⟩ := hstep (N + m) (by omega)
      have hgrow : A.fired (N + (m + 1)) = A.fired (N + m) ++ [e'] := by
        rw [show N + (m + 1) = (N + m) + 1 from rfl, A.fired_succ_of_some hfire]
      rw [hgrow, List.filter_append]
      simp only [List.length_append, List.filter_cons, decide_eq_true_eq, hlt,
        List.filter_nil, if_true, List.length_cons, List.length_nil]
      omega
  have hbound : ∀ s, ((A.fired s).filter fun x ↦ decide (x < e)).length ≤ e := by
    intro s
    have hnd : ((A.fired s).filter fun x ↦ decide (x < e)).Nodup :=
      (A.fired_nodup s).filter _
    have hsub : ((A.fired s).filter fun x ↦ decide (x < e)).toFinset ⊆ Finset.range e := by
      intro x hx
      simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hx
      exact Finset.mem_range.2 hx.2
    calc ((A.fired s).filter fun x ↦ decide (x < e)).length
        = ((A.fired s).filter fun x ↦ decide (x < e)).toFinset.card := by
          rw [List.toFinset_card_of_nodup hnd]
      _ ≤ (Finset.range e).card := Finset.card_le_card hsub
      _ = e := Finset.card_range e
  have h1 := hcount (e + 1)
  have h2 := hbound (N + (e + 1))
  omega

end DovetailAvail
