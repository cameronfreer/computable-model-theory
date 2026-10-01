/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Set.Card

/-!
# Finite elimination

The combinatorial core of a requirement that *guesses*: it selects a candidate, keeps it until the
candidate is refuted, and then selects again. Over a fixed prefix, such a requirement makes only
finitely many selections, provided refutation persists, refuted candidates are never selected, each
replaced candidate was refuted by the time it was replaced, and from some stage on every selection
has index at most a supplied bound `B`.

Like `FiniteInjury`, this module is **pure combinatorics**. It has no computability, no model
theory, no scheduler and no attention model.

## The trace

`selected : ℕ → Option ℕ` is a **time-indexed selection trace**: `none` is a silent stage, and
`some c` means candidate `c` is selected at that stage. Silent stages are allowed anywhere, and the
replacement discipline constrains only the **next** selection after a given one. Later selections
follow from persistence (`refuted_of_lt`).

## The bound is supplied, and the selection is not monotone

The eventual bound `B` is a **hypothesis**. That some genuine, never-refuted candidate `c*` makes
`B := c*` hold is the consumer's proof obligation (for Theorem 3.12, AP on an actual span); it is
not assumed here.

Nothing requires selections to *increase*. A larger candidate may be selected first, refuted, and
replaced by a smaller one that became available only later. Finite elimination needs only
**non-repetition** together with the bound: the selections after the cutoff are pairwise distinct
elements of `{0, …, B}`.

## What this does not claim

There is no claim about the finite-injury kernel's `EventuallySilent`. A kernel priority also acts
through other installations and charged clearings, and relating those actions to a selection trace
is a separate accounting argument, owned by the construction that consumes this.
-/

namespace FiniteElimination

variable (refuted : ℕ → ℕ → Prop) (selected : ℕ → Option ℕ)

/-- **Refutation persists**: once a candidate is refuted, it stays refuted. -/
def Persistent : Prop :=
  ∀ ⦃s t c : ℕ⦄, s ≤ t → refuted s c → refuted t c

/-- **Already-refuted candidates are rejected**: no candidate is selected at a stage where it is
already refuted. -/
def RejectsRefuted : Prop :=
  ∀ ⦃t c : ℕ⦄, selected t = some c → ¬ refuted t c

/-- **The replacement discipline**: the candidate selected at `t` is refuted by the stage of the
*next* selection after `t`. Silent stages in between are allowed. -/
def ReplacesRefuted : Prop :=
  ∀ ⦃t t' c : ℕ⦄, selected t = some c → t < t' → (selected t').isSome →
    (∀ u, t < u → u < t' → selected u = none) → refuted t' c

/-- **The eventual bound**: from stage `N` on, every selection has index at most `B`. -/
def EventuallyBounded (N B : ℕ) : Prop :=
  ∀ ⦃t c : ℕ⦄, N ≤ t → selected t = some c → c ≤ B

/-- The selection stages at or after `N`. -/
def selectionStagesFrom (N : ℕ) : Set ℕ :=
  {t | N ≤ t ∧ (selected t).isSome}

variable {refuted selected}

/-- **Every later selection finds the earlier candidate refuted**: the next selection refutes it,
and refutation persists. -/
theorem refuted_of_lt (hpers : Persistent refuted) (hrepl : ReplacesRefuted refuted selected)
    {t t' c : ℕ} (hc : selected t = some c) (htt' : t < t') (ht' : (selected t').isSome) :
    refuted t' c := by
  classical
  have hex : ∃ u, t < u ∧ (selected u).isSome := ⟨t', htt', ht'⟩
  have hspec := Nat.find_spec hex
  have hmin : Nat.find hex ≤ t' := Nat.find_min' hex ⟨htt', ht'⟩
  have hbetween : ∀ u, t < u → u < Nat.find hex → selected u = none := by
    intro u htu hu
    by_contra hne
    exact Nat.find_min hex hu ⟨htu, Option.ne_none_iff_isSome.1 hne⟩
  exact hpers hmin (hrepl hc hspec.1 hspec.2 hbetween)

/-- **Non-repetition**: two selections at distinct stages select distinct candidates. -/
theorem ne_of_ne (hpers : Persistent refuted) (hrej : RejectsRefuted refuted selected)
    (hrepl : ReplacesRefuted refuted selected) {t t' c c' : ℕ} (hc : selected t = some c)
    (hc' : selected t' = some c') (htt' : t ≠ t') : c ≠ c' := by
  rcases Nat.lt_or_gt_of_ne htt' with hlt | hgt
  · intro heq
    subst heq
    exact hrej hc' (refuted_of_lt hpers hrepl hc hlt (by rw [hc']; rfl))
  · intro heq
    subst heq
    exact hrej hc (refuted_of_lt hpers hrepl hc' hgt (by rw [hc]; rfl))

/-- The candidate read off a selection stage. -/
private def candidateAt (selected : ℕ → Option ℕ) (t : ℕ) : ℕ :=
  (selected t).getD 0

private theorem selected_eq_candidateAt {t : ℕ} (ht : (selected t).isSome) :
    selected t = some (candidateAt selected t) := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 ht
  simp [candidateAt, hc]

private theorem injOn_candidateAt (hpers : Persistent refuted)
    (hrej : RejectsRefuted refuted selected) (hrepl : ReplacesRefuted refuted selected) (N : ℕ) :
    Set.InjOn (candidateAt selected) (selectionStagesFrom selected N) := by
  intro t ht t' ht' heq
  by_contra hne
  exact ne_of_ne hpers hrej hrepl (selected_eq_candidateAt ht.2)
    (selected_eq_candidateAt ht'.2) hne heq

private theorem mapsTo_range {N B : ℕ} (hbound : EventuallyBounded selected N B) :
    Set.MapsTo (candidateAt selected) (selectionStagesFrom selected N)
      (↑(Finset.range (B + 1)) : Set ℕ) := by
  intro t ht
  have := hbound ht.1 (selected_eq_candidateAt ht.2)
  simp only [Finset.coe_range, Set.mem_Iio]
  omega

/-- **Finitely many selections** after the cutoff. -/
theorem finite_selectionStagesFrom (hpers : Persistent refuted)
    (hrej : RejectsRefuted refuted selected) (hrepl : ReplacesRefuted refuted selected)
    {N B : ℕ} (hbound : EventuallyBounded selected N B) :
    (selectionStagesFrom selected N).Finite :=
  Set.Finite.of_finite_image ((Finset.range (B + 1)).finite_toSet.subset
    (Set.mapsTo_iff_image_subset.1 (mapsTo_range hbound)))
    (injOn_candidateAt hpers hrej hrepl N)

/-- **The count**: at most `B + 1` selection stages at or after the cutoff. -/
theorem ncard_selectionStagesFrom_le (hpers : Persistent refuted)
    (hrej : RejectsRefuted refuted selected) (hrepl : ReplacesRefuted refuted selected)
    {N B : ℕ} (hbound : EventuallyBounded selected N B) :
    (selectionStagesFrom selected N).ncard ≤ B + 1 := by
  have h := Set.ncard_le_ncard_of_injOn (candidateAt selected) (mapsTo_range hbound)
    (injOn_candidateAt hpers hrej hrepl N) (Finset.range (B + 1)).finite_toSet
  rwa [Set.ncard_coe_finset, Finset.card_range] at h

/-- **Eventually no selections**: from some stage on, every stage is silent. -/
theorem eventually_none (hpers : Persistent refuted) (hrej : RejectsRefuted refuted selected)
    (hrepl : ReplacesRefuted refuted selected) {N B : ℕ}
    (hbound : EventuallyBounded selected N B) : ∃ M, ∀ t, M ≤ t → selected t = none := by
  obtain ⟨F, hF⟩ := Set.Finite.exists_finset_coe
    (finite_selectionStagesFrom hpers hrej hrepl hbound)
  refine ⟨max N (F.sup id + 1), fun t ht ↦ ?_⟩
  by_contra hne
  have hmem : t ∈ selectionStagesFrom selected N :=
    ⟨le_trans (le_max_left _ _) ht, Option.ne_none_iff_isSome.1 hne⟩
  have hmemF : t ∈ F := by rw [← Finset.mem_coe, hF]; exact hmem
  have h1 : t ≤ F.sup id := Finset.le_sup (f := id) hmemF
  have h2 := le_trans (le_max_right _ _) ht
  omega

end FiniteElimination
