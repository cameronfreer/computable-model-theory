/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.StagedPartial

/-!
# Two staged approximations of the identity

Fixtures for the staged layer, in the import spine rather than in an audit module: both the
`StagedPartial` and `StagedRace` audits consume them, and an audit module's `.olean` is never built,
so an audit cannot import another audit.

They approximate the **same** partial function at deliberately different speeds — `stagedNow`
discovers everything at stage `0`, `stagedRange` discovers `x` only from stage `x + 1`. That gap is
the whole point: it witnesses that a partial function does not determine a discovery stage, and it
supplies an earlier-right/later-left pair for the racing audit's adversarial gate.
-/

open Encodable

namespace StagedPartialIn

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

@[simp] theorem stagedRange_approx (O : Set (ℕ →. ℕ)) (s x : ℕ) :
    (stagedRange O).approx s x = if x < s then some x else none :=
  rfl

/-- The identity on `ℕ`, discovered immediately. -/
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

@[simp] theorem stagedNow_approx (O : Set (ℕ →. ℕ)) (s x : ℕ) :
    (stagedNow O).approx s x = some x :=
  rfl

end StagedPartialIn
