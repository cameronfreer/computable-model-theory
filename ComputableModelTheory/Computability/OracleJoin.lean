/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.RecursiveIn
import ComputableModelTheory.Computability.RecursiveOrdinals

/-!
# The join of two partial oracles

`join X Y` interleaves two partial oracles on even and odd inputs: `join X Y (2 * n) = X n` and
`join X Y (2 * n + 1) = Y n`. Arbitrary partial oracles are supported; nothing is totalized.

The **universal reduction property** (`recursiveIn_join_iff`) says an oracle set computes the join
exactly when it computes both components. Its two projections are the two directions read at the
join itself (`recursiveIn_left`, `recursiveIn_right`), and the only consequence for the recursive
ordinals drawn here is the automatic inequality

`max (omegaOneOf X) (omegaOneOf Y) ≤ omegaOneOf (join X Y)`

(`omegaOneOf.max_le_join`), by monotonicity. **Equality with the maximum is not asserted.**

The partial-recursiveness proof of the join composes two `RecursiveIn.option_casesOn_right`s: the
first yields `X (n / 2)` on even `n` and a total dummy on odd `n`; binding the second replaces the
dummy by `Y (n / 2)` on odd `n` and passes the first value through on even `n`. No two-branch
partial conditional is introduced.
-/

open Encodable

/-- The join of two partial oracles: `X` on even inputs, `Y` on odd inputs. -/
def join (X Y : ℕ →. ℕ) : ℕ →. ℕ :=
  fun n ↦ if n % 2 = 0 then X (n / 2) else Y (n / 2)

namespace join

variable (X Y : ℕ →. ℕ)

@[simp] theorem two_mul (n : ℕ) : join X Y (2 * n) = X n := by
  simp [join, Nat.mul_div_cancel_left n two_pos]

@[simp] theorem two_mul_add_one (n : ℕ) : join X Y (2 * n + 1) = Y n := by
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  simp [join, h1, h2]

/-- The join computes its left component. -/
theorem recursiveIn_left : RecursiveIn {join X Y} X := by
  have hj : RecursiveIn {join X Y} (join X Y) :=
    RecursiveIn.iff_nat.2 (Nat.RecursiveIn.oracle _ rfl)
  have hd : ComputableIn {join X Y} fun n : ℕ ↦ 2 * n :=
    (Primrec.nat_mul.to_comp.computableIn₂ (O := {join X Y})).comp (ComputableIn.const 2)
      ComputableIn.id
  exact (hj.comp hd).of_eq fun n ↦ two_mul X Y n

/-- The join computes its right component. -/
theorem recursiveIn_right : RecursiveIn {join X Y} Y := by
  have hj : RecursiveIn {join X Y} (join X Y) :=
    RecursiveIn.iff_nat.2 (Nat.RecursiveIn.oracle _ rfl)
  have hd : ComputableIn {join X Y} fun n : ℕ ↦ 2 * n + 1 :=
    (Primrec.succ.to_comp.computableIn (O := {join X Y})).comp
      ((Primrec.nat_mul.to_comp.computableIn₂ (O := {join X Y})).comp (ComputableIn.const 2)
        ComputableIn.id)
  exact (hj.comp hd).of_eq fun n ↦ two_mul_add_one X Y n

/-- Any oracle set computing both components computes the join. -/
theorem recursiveIn_of {O : Set (ℕ →. ℕ)} (hX : RecursiveIn O X) (hY : RecursiveIn O Y) :
    RecursiveIn O (join X Y) := by
  -- the even-selector and odd-selector options
  have hhalf : ComputableIn O fun n : ℕ ↦ n / 2 :=
    (Primrec.nat_div.to_comp.computableIn₂ (O := O)).comp ComputableIn.id (ComputableIn.const 2)
  have heven : ComputableIn O fun n : ℕ ↦ decide (n % 2 = 0) :=
    ((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂ (O := O)).comp
      ((Primrec.nat_mod.to_comp.computableIn₂ (O := O)).comp ComputableIn.id
        (ComputableIn.const 2))
      (ComputableIn.const 0)
  have ho₁ : ComputableIn O fun n : ℕ ↦ (if n % 2 = 0 then some (n / 2) else none : Option ℕ) :=
    ComputableIn.ite (c := fun n : ℕ ↦ n % 2 = 0) heven (ComputableIn.option_some.comp hhalf)
      (ComputableIn.const none)
  have ho₂ : ComputableIn O fun n : ℕ ↦ (if n % 2 = 0 then none else some (n / 2) : Option ℕ) :=
    ComputableIn.ite (c := fun n : ℕ ↦ n % 2 = 0) heven (ComputableIn.const none)
      (ComputableIn.option_some.comp hhalf)
  -- first stage: `X (n / 2)` on even `n`, a dummy on odd `n`
  have h₁ : RecursiveIn O fun n : ℕ ↦
      Option.casesOn (motive := fun _ ↦ Part ℕ) (if n % 2 = 0 then some (n / 2) else none)
        (Part.some 0) X :=
    RecursiveIn.option_casesOn_right ho₁ (ComputableIn.const 0)
      (hX.comp ComputableIn.snd).to₂
  -- second stage: `Y (n / 2)` on odd `n`, pass-through on even `n`
  have h₂ : RecursiveIn₂ O fun (n : ℕ) (v : ℕ) ↦
      Option.casesOn (motive := fun _ ↦ Part ℕ) (if n % 2 = 0 then none else some (n / 2))
        (Part.some v) Y :=
    (RecursiveIn.option_casesOn_right (o := fun p : ℕ × ℕ ↦
        (if p.1 % 2 = 0 then none else some (p.1 / 2) : Option ℕ))
      (f := fun p : ℕ × ℕ ↦ p.2) (g := fun _ m ↦ Y m) (ho₂.comp ComputableIn.fst)
      ComputableIn.snd (hY.comp ComputableIn.snd).to₂).to₂
  refine (RecursiveIn.bind h₁ h₂).of_eq fun n ↦ ?_
  by_cases h : n % 2 = 0
  · simp [join, h]
  · simp [join, h]

/-- **The universal reduction property**: an oracle set computes the join iff it computes both
components. -/
theorem recursiveIn_join_iff {O : Set (ℕ →. ℕ)} :
    RecursiveIn O (join X Y) ↔ RecursiveIn O X ∧ RecursiveIn O Y :=
  ⟨fun h ↦ ⟨RecursiveIn.subst (recursiveIn_left X Y) (fun _ hg ↦ by
      rw [Set.mem_singleton_iff] at hg; subst hg; exact h),
    RecursiveIn.subst (recursiveIn_right X Y) (fun _ hg ↦ by
      rw [Set.mem_singleton_iff] at hg; subst hg; exact h)⟩,
    fun ⟨hX, hY⟩ ↦ recursiveIn_of X Y hX hY⟩

end join

namespace omegaOneOf

/-- **The automatic join bound**: both boundaries are at most the join's. Equality with the maximum
is **not** claimed. -/
theorem max_le_join (X Y : ℕ →. ℕ) :
    max (omegaOneOf X) (omegaOneOf Y) ≤ omegaOneOf (join X Y) :=
  max_le (mono (join.recursiveIn_left X Y)) (mono (join.recursiveIn_right X Y))

end omegaOneOf
