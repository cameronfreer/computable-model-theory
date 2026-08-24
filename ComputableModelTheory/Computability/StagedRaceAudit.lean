/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.StagedRace
import ComputableModelTheory.Computability.StagedPartialExample
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: racing two staged approximations

**The load-bearing row is adversarial.** `test_later_left_does_not_displace_earlier_right` fixes a
right side that appears at stage `0` and a left side that appears only at stage `2`, and checks
that the race still reports the *right* value at stage `5` — long after the left side has arrived.
A current-stage left-biased `orElse` fails exactly this: it would say right at stage `0` and left
at stage `2`, so the tag would not be stable and no consumer could act on it.
`test_orElse_would_flip` records that failure concretely, on the same data.

`test_generic_adversarial` is the same guarantee without a fixture, so the property is not an
accident of the two approximations chosen.

**The off-by-one is gated.** `test_stage_participates` checks that a side appearing exactly at
stage `s` is visible at stage `s` — the reason the bounded search runs over `List.range (s + 1)`.
Searching `List.range s` would make the approximation lag its own index, and every other row here
would still pass.

**The tie rule is gated separately from the ordering.** `test_tie_prefers_left` pins that
simultaneous arrival goes left; the adversarial rows pin that *earlier* beats *preferred*. Together
they say the order of the two criteria is earliest-first, preference-second.

`test_relative_without_merge` records what the construction cost: the raced function is
`RecursiveIn O` outright, by `rfind` on `hit`. Neither `RecursiveIn.merge'` nor `Partrec.race`
appears in this tranche, and neither is needed.
-/

open Encodable

namespace StagedPartialIn

/-! ### The fixtures

`stagedNow` discovers everything at stage `0`; `stagedRange` discovers `x` only from stage `x + 1`.
At input `1` that is stage `0` against stage `2` — an earlier right and a later left. -/

/-- The left side, late: at input `1` it appears only from stage `2`. -/
private noncomputable def slowLeft (O : Set (ℕ →. ℕ)) := stagedRange O

/-- The right side, immediate: at input `1` it appears at stage `0`. -/
private noncomputable def fastRight (O : Set (ℕ →. ℕ)) := stagedNow O

/-! ### The adversarial guarantee -/

/-- **A later left result does not displace an earlier right result.** The right side arrives at
stage `0`; the left side arrives at stage `2`; at stage `5` the race still reports the right side.

This is the row a current-stage `orElse` cannot satisfy. -/
theorem test_later_left_does_not_displace_earlier_right (O : Set (ℕ →. ℕ)) :
    ((slowLeft O).race (fastRight O)).approx 5 1 = some (false, 1) := by
  obtain ⟨z, hz⟩ :=
    approx_eq_right_of_right_earlier (slowLeft O) (fastRight O)
      (t₀ := 0) (x := 1) (by simp [fastRight])
      (fun u hu ↦ by
        obtain rfl : u = 0 := Nat.le_zero.1 hu
        simp [slowLeft])
      (by omega)
  have hmem : ((false, z) : Bool × ℕ) ∈ (slowLeft O).raceFun (fastRight O) 1 :=
    ((slowLeft O).race (fastRight O)).sound hz
  have hz1 : z = 1 :=
    Part.mem_some_iff.1 ((slowLeft O).mem_right_of_mem_raceFun (fastRight O) hmem)
  rw [hz, hz1]

/-- **And the left side really has arrived by then**, so the row above is not vacuous: at stage `5`
the left value is available and is still not reported. -/
theorem test_left_has_arrived (O : Set (ℕ →. ℕ)) :
    (slowLeft O).approx 5 1 = some 1 ∧ (fastRight O).approx 0 1 = some 1 :=
  ⟨by simp [slowLeft], by simp [fastRight]⟩

/-- **What the naive definition would have done.** On the same data, a current-stage left-biased
`orElse` reports the right side at stage `0` and the left side at stage `2` — a tag that moves, and
therefore is not information. -/
theorem test_orElse_would_flip (O : Set (ℕ →. ℕ)) :
    (((slowLeft O).approx 0 1).map (fun y ↦ (true, y))).or
        (((fastRight O).approx 0 1).map fun z ↦ (false, z)) = some (false, 1) ∧
      (((slowLeft O).approx 2 1).map (fun y ↦ (true, y))).or
        (((fastRight O).approx 2 1).map fun z ↦ (false, z)) = some (true, 1) := by
  constructor
  · simp [slowLeft, fastRight]
  · simp [slowLeft, fastRight]

/-- The guarantee generically, so it is not an artifact of these two approximations. -/
theorem test_generic_adversarial {α β : Type*} [Primcodable α] [Primcodable β]
    {O : Set (ℕ →. ℕ)} {f g : α →. β} (F : StagedPartialIn O f) (G : StagedPartialIn O g)
    {x : α} {t₀ : ℕ} (hG : (G.approx t₀ x).isSome) (hF : ∀ u, u ≤ t₀ → F.approx u x = none)
    {s : ℕ} (hs : t₀ ≤ s) : ∃ z, (F.race G).approx s x = some (false, z) :=
  approx_eq_right_of_right_earlier F G hG hF hs

/-! ### The off-by-one, and the tie rule -/

/-- **Stage `s` participates in its own search.** The left side of `stagedRange` appears exactly at
stage `x + 1`, and the race sees it there — not one stage later. Searching `List.range s` instead of
`List.range (s + 1)` would break this and nothing else here. -/
theorem test_stage_participates (O : Set (ℕ →. ℕ)) :
    ((slowLeft O).race (slowLeft O)).approx 1 1 = none ∧
      (((slowLeft O).race (slowLeft O)).approx 2 1).isSome := by
  refine ⟨approx_eq_none_of_no_hit (slowLeft O) (slowLeft O) fun t ht ↦ ?_,
    approx_isSome_of_hit (slowLeft O) (slowLeft O) (t₀ := 2) ?_ (by omega)⟩
  · have : ¬ (1 < t) := by omega
    simp [hit, slowLeft, this]
  · simp [hit, slowLeft]

/-- **The tie rule.** Where both sides have appeared at the same stage, the left one is
reported — so the ordering criterion is earliest-first and preference only breaks ties. -/
theorem test_tie_prefers_left {α β : Type*} [Primcodable α] [Primcodable β]
    {O : Set (ℕ →. ℕ)} {f g : α →. β} (F : StagedPartialIn O f) (G : StagedPartialIn O g)
    {t : ℕ} {x : α} {y : β} (h : F.approx t x = some y) :
    F.pick G t x = some (true, y) :=
  pick_eq_left F G h

/-! ### What the race computes -/

/-- Tags are sound on both sides. -/
theorem test_tags_are_sound {α β : Type*} [Primcodable α] [Primcodable β]
    {O : Set (ℕ →. ℕ)} {f g : α →. β} (F : StagedPartialIn O f) (G : StagedPartialIn O g)
    {x : α} {y z : β} :
    ((true, y) ∈ F.raceFun G x → y ∈ f x) ∧ ((false, z) ∈ F.raceFun G x → z ∈ g x) :=
  ⟨F.mem_left_of_mem_raceFun G, F.mem_right_of_mem_raceFun G⟩

/-- The race halts exactly when one side does. -/
theorem test_race_dom_iff {α β : Type*} [Primcodable α] [Primcodable β]
    {O : Set (ℕ →. ℕ)} {f g : α →. β} (F : StagedPartialIn O f) (G : StagedPartialIn O g)
    {x : α} : (F.raceFun G x).Dom ↔ (f x).Dom ∨ (g x).Dom :=
  F.raceFun_dom_iff G

/-- **A genuinely relative construction.** The raced function is `RecursiveIn O` outright — by
`rfind` on `hit`, then reading the tagged value at the stage found. No `RecursiveIn.merge'` and no
`Partrec.race` appear in this tranche, and neither is needed. -/
theorem test_relative_without_merge {α β : Type*} [Primcodable α] [Primcodable β]
    {O : Set (ℕ →. ℕ)} {f g : α →. β} (F : StagedPartialIn O f) (G : StagedPartialIn O g) :
    RecursiveIn O (F.raceFun G) :=
  F.raceFun_recursiveIn G

end StagedPartialIn

#assert_standard_axioms
  StagedPartialIn.test_later_left_does_not_displace_earlier_right
#assert_standard_axioms StagedPartialIn.test_left_has_arrived
#assert_standard_axioms StagedPartialIn.test_orElse_would_flip
#assert_standard_axioms StagedPartialIn.test_generic_adversarial
#assert_standard_axioms StagedPartialIn.test_stage_participates
#assert_standard_axioms StagedPartialIn.test_tie_prefers_left
#assert_standard_axioms StagedPartialIn.test_tags_are_sound
#assert_standard_axioms StagedPartialIn.test_race_dom_iff
#assert_standard_axioms StagedPartialIn.test_relative_without_merge
