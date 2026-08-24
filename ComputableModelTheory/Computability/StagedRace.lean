/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.StagedPartial
import ComputableModelTheory.Computability.ListPredicates

/-!
# Racing two staged approximations, by earliest discovery

The first consumer of `StagedPartialIn`: given staged approximations of two partial functions,
produce a staged approximation of a **tagged** race — the value of whichever side appears first,
labelled with the side that produced it. A priority construction needs the tag, since it must know
which requirement fired.

## Why the obvious definition is wrong

The tempting approximation is "look at stage `s` and prefer the left side" —
`(F.approx s x).orElse (G.approx s x)` with a tag. **That is not monotone.** If the right side
appears at stage `s` and the left only later, the tagged output at stage `s` says *right* and at a
later stage says *left*, so the tag is not stable information and nothing downstream may rely on
it. `StagedPartialAudit.test_stage_is_not_determined` is the concrete witness that this can happen:
two staged approximations of the *same* function can discover a value at different stages.

## What is done instead

The winner is decided by **earliest discovery stage**, with a fixed left-preference tie rule, and
that winner is then permanent:

* `hit t x` — either side has appeared by stage `t`;
* `pick t x` — the tagged value at stage `t`, left preferred;
* the approximation at stage `s` selects the **least** `t ≤ s` with `hit t x`, and reads `pick`
  there.

Because `hit` is monotone and the *least* hit stage is stable once found, the answer never moves.
The bounded search is over `List.range (s + 1)`, not `List.range s`: stage `s` itself must
participate, or the approximation would lag its own index by one.

Everything below consumes a single private specification of the bounded search,

```
firstHit? s x = some t  ↔  t ≤ s ∧ hit t x ∧ ∀ u < t, ¬ hit u x
```

so monotonicity, soundness, completeness and the adversarial guarantee are all statements about
preservation of the *least* hit, not about list arithmetic.

## Relativity

`raceFun` is `RecursiveIn O` by `RecursiveIn.rfind_total` on `hit` followed by reading `pick` at
the found stage. That is a genuinely relative construction, so **`RecursiveIn.merge'` is not needed
and is not introduced**; nor is `Partrec.race`, which stays spike-local. Merge becomes live only if
some consumer must race extensional `RecursiveIn` procedures that carry no staged data.
-/

open Encodable

variable {α β : Type*} [Primcodable α] [Primcodable β]
variable {O : Set (ℕ →. ℕ)} {f g : α →. β}

namespace StagedPartialIn

/-! ### Hitting and picking -/

/-- Either side has appeared by stage `t`. -/
def hit (F : StagedPartialIn O f) (G : StagedPartialIn O g) (t : ℕ) (x : α) : Bool :=
  (F.approx t x).isSome || (G.approx t x).isSome

/-- The tagged value at stage `t`, **left preferred**. `true` tags the left side. -/
def pick (F : StagedPartialIn O f) (G : StagedPartialIn O g) (t : ℕ) (x : α) :
    Option (Bool × β) :=
  match F.approx t x with
  | some y => some (true, y)
  | none => (G.approx t x).map fun z ↦ (false, z)

variable (F : StagedPartialIn O f) (G : StagedPartialIn O g)

theorem hit_of_le {t u : ℕ} {x : α} (h : t ≤ u) (ht : F.hit G t x = true) :
    F.hit G u x = true := by
  rw [hit, Bool.or_eq_true] at ht ⊢
  exact ht.imp (F.isSome_of_le h) (G.isSome_of_le h)

/-- **The tie rule.** Where the left side has appeared, it wins — whatever the right side has
done. -/
theorem pick_eq_left {t : ℕ} {x : α} {y : β} (h : F.approx t x = some y) :
    F.pick G t x = some (true, y) := by
  rw [pick, h]

/-- Where the left side has *not* appeared, the right side is reported. -/
theorem pick_eq_right {t : ℕ} {x : α} (h : F.approx t x = none) :
    F.pick G t x = (G.approx t x).map fun z ↦ (false, z) := by
  rw [pick, h]

theorem pick_isSome_of_hit {t : ℕ} {x : α} (h : F.hit G t x = true) :
    (F.pick G t x).isSome := by
  rw [hit, Bool.or_eq_true] at h
  rcases hF : F.approx t x with - | y
  · rw [pick_eq_right F G hF]
    rcases h with h | h
    · rw [hF] at h; exact absurd h (by simp)
    · obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 h
      rw [hz]; rfl
  · rw [pick_eq_left F G hF]; rfl

theorem hit_of_pick_isSome {t : ℕ} {x : α} (h : (F.pick G t x).isSome) :
    F.hit G t x = true := by
  rw [hit, Bool.or_eq_true]
  rcases hF : F.approx t x with - | y
  · right
    rw [pick_eq_right F G hF, Option.isSome_map] at h
    exact h
  · exact Or.inl rfl

/-! ### The bounded search

The one private helper, and the one specification everything else consumes. -/

/-- The least stage `t ≤ s` at which either side has appeared, if any.

Searched over `List.range (s + 1)` — stage `s` itself must participate. -/
private def firstHit? (s : ℕ) (x : α) : Option ℕ :=
  let k := (List.range (s + 1)).findIdx fun t ↦ F.hit G t x
  if k ≤ s then some k else none

/-- **The specification.** Everything below is a statement about preservation of the least hit;
nothing else reopens the list. -/
private theorem firstHit?_eq_some_iff {s t : ℕ} {x : α} :
    F.firstHit? G s x = some t ↔
      t ≤ s ∧ F.hit G t x = true ∧ ∀ u, u < t → F.hit G u x = false := by
  set k := (List.range (s + 1)).findIdx fun t ↦ F.hit G t x with hk
  have hmin : ∀ u, u < k → F.hit G u x = false := by
    intro u hu
    have hlt : u < (List.range (s + 1)).length := by
      have := List.findIdx_le_length (p := fun t ↦ F.hit G t x) (xs := List.range (s + 1))
      simp only [List.length_range] at this ⊢
      omega
    have hnot := List.not_of_lt_findIdx (p := fun t ↦ F.hit G t x) (xs := List.range (s + 1)) hu
    simpa [List.getElem_range] using hnot
  constructor
  · intro h
    rw [firstHit?] at h
    by_cases hks : k ≤ s
    · rw [if_pos hks] at h
      obtain rfl : k = t := Option.some.inj h
      refine ⟨hks, ?_, hmin⟩
      have hlt : k < s + 1 := by omega
      have hget : (List.range (s + 1))[k]? = some k := List.getElem?_range (by simpa using hlt)
      exact List.findIdx_of_getElem?_eq_some (p := fun t ↦ F.hit G t x) hget
    · rw [if_neg hks] at h
      exact absurd h (by simp)
  · rintro ⟨hts, hhit, hlt⟩
    have hkt : k ≤ t := by
      by_contra hgt
      exact absurd hhit (by rw [hmin t (Nat.lt_of_not_le hgt)]; simp)
    have htk : t ≤ k := by
      by_contra hgt
      have hklt : k < t := Nat.lt_of_not_le hgt
      have hlen : k < (List.range (s + 1)).length := by
        simp only [List.length_range]; omega
      have hget : (List.range (s + 1))[k]? = some k := List.getElem?_range (by simpa using hlen)
      have := List.findIdx_of_getElem?_eq_some (p := fun t ↦ F.hit G t x) hget
      exact absurd this (by rw [hlt k hklt]; simp)
    have hkt' : k = t := Nat.le_antisymm hkt htk
    rw [firstHit?, ← hk, hkt', if_pos hts]

/-! ### The race -/

/-- **The raced partial function**: the tagged value at the least stage either side appears. -/
noncomputable def raceFun (x : α) : Part (Bool × β) :=
  (Nat.rfind fun t ↦ Part.some (F.hit G t x)).bind fun t ↦
    ((F.pick G t x : Option (Bool × β)) : Part (Bool × β))

/-- Membership in the race, in terms of the least hit. -/
theorem mem_raceFun_iff {x : α} {v : Bool × β} :
    v ∈ F.raceFun G x ↔
      ∃ t, F.hit G t x = true ∧ (∀ u, u < t → F.hit G u x = false) ∧
        F.pick G t x = some v := by
  rw [raceFun]
  constructor
  · intro h
    obtain ⟨t, ht, hv⟩ := Part.mem_bind_iff.1 h
    rw [Nat.mem_rfind] at ht
    refine ⟨t, ?_, ?_, ?_⟩
    · exact Part.mem_some_iff.1 ht.1 |>.symm
    · intro u hu
      exact (Part.mem_some_iff.1 (ht.2 hu)).symm
    · rw [Part.mem_ofOption, Option.mem_def] at hv
      exact hv
  · rintro ⟨t, hhit, hmin, hpick⟩
    refine Part.mem_bind_iff.2 ⟨t, ?_, ?_⟩
    · rw [Nat.mem_rfind]
      exact ⟨Part.mem_some_iff.2 hhit.symm, fun {u} hu ↦ Part.mem_some_iff.2 (hmin u hu).symm⟩
    · rw [Part.mem_ofOption, Option.mem_def]
      exact hpick

/-- **The staged race.** Its approximation at stage `s` is the tagged value at the least hit stage
`t ≤ s` — not the value at stage `s`. -/
noncomputable def race : StagedPartialIn O (F.raceFun G) where
  approx s x := (F.firstHit? G s x).bind fun t ↦ F.pick G t x
  approx_computableIn := by
    -- every stage of the pipeline is a fully pinned composition
    have hFapp : ComputableIn O fun r : (ℕ × α) × ℕ ↦ F.approx r.2 r.1.2 :=
      F.approx_computableIn.comp (ComputableIn.snd.pair (ComputableIn.snd.comp ComputableIn.fst))
    have hGapp : ComputableIn O fun r : (ℕ × α) × ℕ ↦ G.approx r.2 r.1.2 :=
      G.approx_computableIn.comp (ComputableIn.snd.pair (ComputableIn.snd.comp ComputableIn.fst))
    have hhit : ComputableIn₂ O fun (q : ℕ × α) (t : ℕ) ↦ F.hit G t q.2 :=
      ((Primrec.or.to_comp.computableIn₂ (O := O)).comp
        ((Primrec.option_isSome.to_comp.computableIn (O := O)).comp hFapp)
        ((Primrec.option_isSome.to_comp.computableIn (O := O)).comp hGapp)).to₂
    have hrange : ComputableIn O fun q : ℕ × α ↦ List.range (q.1 + 1) :=
      (Primrec.list_range.to_comp.computableIn (O := O)).comp
        ((Primrec.succ.to_comp.computableIn (O := O)).comp ComputableIn.fst)
    have hidx : ComputableIn O fun q : ℕ × α ↦
        (List.range (q.1 + 1)).findIdx fun t ↦ F.hit G t q.2 :=
      ComputableIn.list_findIdx hrange hhit
    have hfirst : ComputableIn O fun q : ℕ × α ↦ F.firstHit? G q.1 q.2 := by
      have hcond : ComputableIn O fun q : ℕ × α ↦
          decide ((List.range (q.1 + 1)).findIdx (fun t ↦ F.hit G t q.2) ≤ q.1) :=
        (Primrec.nat_le.decide.to_comp.computableIn₂ (O := O)).comp hidx ComputableIn.fst
      exact (ComputableIn.cond hcond (ComputableIn.option_some.comp hidx)
        (ComputableIn.const Option.none)).of_eq fun q ↦ by
          rw [firstHit?]
          by_cases hq : (List.range (q.1 + 1)).findIdx (fun t ↦ F.hit G t q.2) ≤ q.1 <;>
            simp [hq]
    have hpick : ComputableIn₂ O fun (q : ℕ × α) (t : ℕ) ↦ F.pick G t q.2 := by
      have hmapped : ComputableIn O fun r : (ℕ × α) × ℕ ↦
          (G.approx r.2 r.1.2).map fun z ↦ ((false, z) : Bool × β) :=
        ComputableIn.option_map hGapp
          (((ComputableIn.const false).pair ComputableIn.snd).to₂)
      have hsome : ComputableIn₂ O fun (r : (ℕ × α) × ℕ) (y : β) ↦
          (Option.some (true, y) : Option (Bool × β)) :=
        (ComputableIn.option_some.comp ((ComputableIn.const true).pair ComputableIn.snd)).to₂
      have hcases : ComputableIn O fun r : (ℕ × α) × ℕ ↦ F.pick G r.2 r.1.2 :=
        (ComputableIn.option_casesOn hFapp hmapped hsome).of_eq fun r ↦ by
          rw [pick]
          cases F.approx r.2 r.1.2 <;> rfl
      exact hcases.to₂
    exact ComputableIn.option_bind hfirst hpick
  sound := by
    intro s x v h
    obtain ⟨t, ht, hpick⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨-, hhit, hmin⟩ := (firstHit?_eq_some_iff F G).1 ht
    exact (mem_raceFun_iff F G).2 ⟨t, hhit, hmin, hpick⟩
  monotone := by
    intro s s' x v hss h
    obtain ⟨t, ht, hpick⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨hts, hhit, hmin⟩ := (firstHit?_eq_some_iff F G).1 ht
    have ht' : F.firstHit? G s' x = some t :=
      (firstHit?_eq_some_iff F G).2 ⟨Nat.le_trans hts hss, hhit, hmin⟩
    rw [ht']
    exact hpick
  complete := by
    intro x v h
    obtain ⟨t, hhit, hmin, hpick⟩ := (mem_raceFun_iff F G).1 h
    refine ⟨t, ?_⟩
    rw [(firstHit?_eq_some_iff F G).2 ⟨Nat.le_refl t, hhit, hmin⟩]
    exact hpick


@[simp] private theorem race_approx (s : ℕ) (x : α) :
    (F.race G).approx s x = (F.firstHit? G s x).bind fun t ↦ F.pick G t x :=
  rfl

/-! ### What the race computes -/

/-- **The race is partial recursive in the oracle**, by `rfind` on `hit` and then reading `pick` at
the stage found. A genuinely relative construction: no `merge'`, relative or otherwise. -/
theorem raceFun_recursiveIn : RecursiveIn O (F.raceFun G) := by
  have hFapp : ComputableIn O fun r : α × ℕ ↦ F.approx r.2 r.1 :=
    F.approx_computableIn.comp (ComputableIn.snd.pair ComputableIn.fst)
  have hGapp : ComputableIn O fun r : α × ℕ ↦ G.approx r.2 r.1 :=
    G.approx_computableIn.comp (ComputableIn.snd.pair ComputableIn.fst)
  have hhit : ComputableIn₂ O fun (x : α) (t : ℕ) ↦ F.hit G t x :=
    ((Primrec.or.to_comp.computableIn₂ (O := O)).comp
      ((Primrec.option_isSome.to_comp.computableIn (O := O)).comp hFapp)
      ((Primrec.option_isSome.to_comp.computableIn (O := O)).comp hGapp)).to₂
  have hpick : ComputableIn O fun r : α × ℕ ↦ F.pick G r.2 r.1 := by
    have hmapped : ComputableIn O fun r : α × ℕ ↦
        (G.approx r.2 r.1).map fun z ↦ ((false, z) : Bool × β) :=
      ComputableIn.option_map hGapp (((ComputableIn.const false).pair ComputableIn.snd).to₂)
    have hsome : ComputableIn₂ O fun (r : α × ℕ) (y : β) ↦
        (Option.some (true, y) : Option (Bool × β)) :=
      (ComputableIn.option_some.comp ((ComputableIn.const true).pair ComputableIn.snd)).to₂
    exact (ComputableIn.option_casesOn hFapp hmapped hsome).of_eq fun r ↦ by
      rw [pick]
      cases F.approx r.2 r.1 <;> rfl
  exact RecursiveIn.bind (RecursiveIn.rfind_total hhit) (ComputableIn.ofOption hpick).to₂

/-- A `true` tag really is a left value. -/
theorem mem_left_of_mem_raceFun {x : α} {y : β} (h : (true, y) ∈ F.raceFun G x) : y ∈ f x := by
  obtain ⟨t, -, -, hpick⟩ := (mem_raceFun_iff F G).1 h
  rcases hF : F.approx t x with - | y'
  · rw [pick_eq_right F G hF] at hpick
    obtain ⟨z, -, hz⟩ := Option.map_eq_some_iff.1 hpick
    exact absurd hz (by simp)
  · rw [pick_eq_left F G hF] at hpick
    obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hpick
    exact F.sound hF

/-- A `false` tag really is a right value. -/
theorem mem_right_of_mem_raceFun {x : α} {z : β} (h : (false, z) ∈ F.raceFun G x) : z ∈ g x := by
  obtain ⟨t, -, -, hpick⟩ := (mem_raceFun_iff F G).1 h
  rcases hF : F.approx t x with - | y'
  · rw [pick_eq_right F G hF] at hpick
    obtain ⟨z', hz', hz⟩ := Option.map_eq_some_iff.1 hpick
    obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ hz
    exact G.sound hz'
  · rw [pick_eq_left F G hF] at hpick
    exact absurd (Option.some.inj hpick) (by simp)

/-- The race halts exactly when one of the two sides does. -/
theorem raceFun_dom_iff {x : α} : (F.raceFun G x).Dom ↔ (f x).Dom ∨ (g x).Dom := by
  classical
  constructor
  · intro h
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.1 h
    obtain ⟨t, hhit, -, -⟩ := (mem_raceFun_iff F G).1 hv
    rw [hit, Bool.or_eq_true] at hhit
    rcases hhit with hF | hG
    · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hF
      exact Or.inl (F.dom_iff_exists_approx.2 ⟨t, y, hy⟩)
    · obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 hG
      exact Or.inr (G.dom_iff_exists_approx.2 ⟨t, z, hz⟩)
  · intro h
    have hex : ∃ u, F.hit G u x = true := by
      rcases h with h | h
      · obtain ⟨s, y, hy⟩ := F.dom_iff_exists_approx.1 h
        exact ⟨s, by rw [hit, hy]; simp⟩
      · obtain ⟨s, z, hz⟩ := G.dom_iff_exists_approx.1 h
        exact ⟨s, by rw [hit, hz]; simp⟩
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (pick_isSome_of_hit F G (Nat.find_spec hex))
    refine Part.dom_iff_mem.2 ⟨v, (mem_raceFun_iff F G).2 ⟨Nat.find hex, Nat.find_spec hex,
      fun u hu ↦ ?_, hv⟩⟩
    simpa using Nat.find_min hex hu

/-- **A hit at stage `t₀` is visible from stage `t₀` on** — in particular at `t₀` itself, which is
why the bounded search runs over `List.range (s + 1)`. -/
theorem approx_isSome_of_hit {x : α} {t₀ s : ℕ} (h : F.hit G t₀ x = true) (hs : t₀ ≤ s) :
    ((F.race G).approx s x).isSome := by
  classical
  have hex : ∃ u, F.hit G u x = true := ⟨t₀, h⟩
  have hmin : ∀ u, u < Nat.find hex → F.hit G u x = false := fun u hu ↦ by
    simpa using Nat.find_min hex hu
  rw [race_approx, (firstHit?_eq_some_iff F G).2
    ⟨Nat.le_trans (Nat.find_le h) hs, Nat.find_spec hex, hmin⟩, Option.bind_some]
  exact pick_isSome_of_hit F G (Nat.find_spec hex)

/-- **And nothing is reported before the first hit.** -/
theorem approx_eq_none_of_no_hit {x : α} {s : ℕ} (h : ∀ t, t ≤ s → F.hit G t x = false) :
    (F.race G).approx s x = none := by
  rcases hfirst : F.firstHit? G s x with - | t
  · rw [race_approx, hfirst]; rfl
  · obtain ⟨hts, hhit, -⟩ := (firstHit?_eq_some_iff F G).1 hfirst
    exact absurd hhit (by rw [h t hts]; simp)

/-! ### The adversarial guarantee -/

/-- **A later left result does not displace an earlier right result.**

If the right side has appeared by stage `t₀` and the left side has appeared at *no* stage `≤ t₀`,
then from stage `t₀` on the race reports the right side — whatever the left side does afterwards.
This is the property a current-stage left-biased `orElse` fails. -/
theorem approx_eq_right_of_right_earlier {x : α} {t₀ : ℕ}
    (hG : (G.approx t₀ x).isSome) (hF : ∀ u, u ≤ t₀ → F.approx u x = none) {s : ℕ} (hs : t₀ ≤ s) :
    ∃ z, (F.race G).approx s x = some (false, z) := by
  classical
  have hex : ∃ u, F.hit G u x = true := ⟨t₀, by rw [hit, Bool.or_eq_true]; exact Or.inr hG⟩
  have hhit : F.hit G (Nat.find hex) x = true := Nat.find_spec hex
  have hmin : ∀ u, u < Nat.find hex → F.hit G u x = false := fun u hu ↦ by
    simpa using Nat.find_min hex hu
  have hle : Nat.find hex ≤ t₀ :=
    Nat.find_le (by rw [hit, Bool.or_eq_true]; exact Or.inr hG)
  have hFnone : F.approx (Nat.find hex) x = none := hF _ hle
  rw [hit, hFnone, Bool.or_eq_true] at hhit
  have hGsome : (G.approx (Nat.find hex) x).isSome := by
    rcases hhit with h | h
    · exact absurd h (by simp)
    · exact h
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 hGsome
  refine ⟨z, ?_⟩
  rw [race_approx, (firstHit?_eq_some_iff F G).2 ⟨Nat.le_trans hle hs, Nat.find_spec hex, hmin⟩,
    Option.bind_some, pick_eq_right F G hFnone, hz]
  rfl

end StagedPartialIn
