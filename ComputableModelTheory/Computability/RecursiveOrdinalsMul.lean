/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.SetTheory.Ordinal.Arithmetic
import ComputableModelTheory.Computability.RecursiveOrdinals

/-!
# `ω · β` from a presentation of `β`

`RecWellOrder.mulOmega W` presents `ω · W.type`: its domain is the set of codes `Nat.pair b n` with
`b` in `W`'s domain and `n` arbitrary, ordered lexicographically with the **first** coordinate most
significant — `W`'s order on `b`, then `<` on `n`. That is `W.type` copies of `ω` laid end to end,
whose type is `ω · W.type` (`type_prod_lex`: the type of `Prod.Lex s r` is `type r * type s`, the
second coordinate's type times the first's).

The order of multiplication matters and is checked in the audit: with `β = 2` the constructed type
is `ω · 2 = ω + ω`, not `2 · ω = ω`, and all of copy `0` lies below all of copy `1`.

`RecOrdinals.omega0_mul_mem` and `omegaOneOf.omega0_mul_lt` are the consequences for the boundary:
`β < omegaOneOf X → ω · β < omegaOneOf X`, derived from representability — not from limit-ness,
and not from any countable-supremum closure.
-/

open Encodable Ordinal

namespace RecWellOrder

variable {X : ℕ →. ℕ} (W : RecWellOrder X)

/-- The domain of `ω · W`: codes of pairs whose first coordinate lies in `W`'s domain. -/
def mulOmegaDomain : Set ℕ := {m | (Nat.unpair m).1 ∈ W.domain}

/-- The order of `ω · W`: compare first coordinates by `W`, then second coordinates by `<`. -/
def mulOmegaRel (a b : ℕ) : Prop :=
  W.rel (Nat.unpair a).1 (Nat.unpair b).1 ∨
    ((Nat.unpair a).1 = (Nat.unpair b).1 ∧ (Nat.unpair a).2 < (Nat.unpair b).2)

/-- The domain of `ω · W`, as `W.domain × ℕ`. -/
def mulOmegaEquiv : W.domain × ℕ ≃ W.mulOmegaDomain where
  toFun p := ⟨Nat.pair p.1.1 p.2, by simp [mulOmegaDomain, Nat.unpair_pair, p.1.2]⟩
  invFun m := (⟨(Nat.unpair m.1).1, m.2⟩, (Nat.unpair m.1).2)
  left_inv p := by simp [Nat.unpair_pair]
  right_inv m := Subtype.ext (Nat.pair_unpair m.1)

/-- The order of `ω · W` is the lexicographic product, first coordinate most significant. -/
def mulOmegaRelIso :
    Prod.Lex (Subrel W.rel (· ∈ W.domain)) ((· < ·) : ℕ → ℕ → Prop) ≃r
      Subrel W.mulOmegaRel (· ∈ W.mulOmegaDomain) where
  toEquiv := W.mulOmegaEquiv
  map_rel_iff' := by
    rintro ⟨⟨a, ha⟩, n⟩ ⟨⟨b, hb⟩, k⟩
    change W.mulOmegaRel (Nat.pair a n) (Nat.pair b k) ↔
      Prod.Lex (Subrel W.rel (· ∈ W.domain)) (· < ·) (⟨a, ha⟩, n) (⟨b, hb⟩, k)
    simp only [mulOmegaRel, Nat.unpair_pair, Prod.lex_def, Subrel, Subtype.mk.injEq]
    rfl

instance isWellOrder_mulOmega :
    IsWellOrder W.mulOmegaDomain (Subrel W.mulOmegaRel (· ∈ W.mulOmegaDomain)) :=
  W.mulOmegaRelIso.symm.toRelEmbedding.isWellOrder

private theorem mulOmegaDomain_computable : ComputablePredIn {X} (· ∈ W.mulOmegaDomain) :=
  (W.domain_computable.comp
    ((Primrec.fst.to_comp.computableIn (O := {X})).comp
      (Primrec.unpair.to_comp.computableIn (O := {X})))).of_eq fun _ ↦ Iff.rfl

private theorem mulOmegaRel_computable : ComputableRelIn {X} W.mulOmegaRel := by
  have hu₁ : ComputableIn {X} fun m : ℕ ↦ (Nat.unpair m).1 :=
    (Primrec.fst.to_comp.computableIn (O := {X})).comp (Primrec.unpair.to_comp.computableIn)
  have hu₂ : ComputableIn {X} fun m : ℕ ↦ (Nat.unpair m).2 :=
    (Primrec.snd.to_comp.computableIn (O := {X})).comp (Primrec.unpair.to_comp.computableIn)
  have hrel : ComputablePredIn {X} fun x : ℕ × ℕ ↦
      W.rel (Nat.unpair x.1).1 (Nat.unpair x.2).1 :=
    W.rel_computable.comp ((hu₁.comp ComputableIn.fst).pair (hu₁.comp ComputableIn.snd))
  have heq : ComputablePredIn {X} fun x : ℕ × ℕ ↦ (Nat.unpair x.1).1 = (Nat.unpair x.2).1 :=
    ComputableIn.computablePredIn
      (((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂ (O := {X})).comp
        (hu₁.comp ComputableIn.fst) (hu₁.comp ComputableIn.snd))
  have hlt : ComputablePredIn {X} fun x : ℕ × ℕ ↦ (Nat.unpair x.1).2 < (Nat.unpair x.2).2 :=
    ComputableIn.computablePredIn
      ((Primrec.nat_lt.decide.to_comp.computableIn₂ (O := {X})).comp
        (hu₂.comp ComputableIn.fst) (hu₂.comp ComputableIn.snd))
  exact (hrel.or (heq.and hlt)).of_eq fun _ ↦ Iff.rfl

/-- **`ω · W`**: `W.type` copies of `ω`, end to end. -/
def mulOmega : RecWellOrder X where
  domain := W.mulOmegaDomain
  domain_computable := W.mulOmegaDomain_computable
  rel := W.mulOmegaRel
  rel_computable := W.mulOmegaRel_computable
  isWellOrder := W.isWellOrder_mulOmega

/-- The constructed presentation has type `ω · W.type` — `ω` times the number of copies, in that
order. -/
theorem type_mulOmega : W.mulOmega.type = ω * W.type := by
  change Ordinal.type (Subrel W.mulOmegaRel (· ∈ W.mulOmegaDomain)) = _
  rw [← W.mulOmegaRelIso.ordinalType_congr, type_prod_lex, type_nat_lt]
  rfl

end RecWellOrder

namespace RecOrdinals

variable {X : ℕ →. ℕ}

/-- Presented ordinals are closed under left multiplication by `ω`. -/
theorem omega0_mul_mem {α : Ordinal.{0}} (h : α ∈ RecOrdinals X) : ω * α ∈ RecOrdinals X := by
  obtain ⟨W, rfl⟩ := h
  exact ⟨W.mulOmega, W.type_mulOmega⟩

end RecOrdinals

namespace omegaOneOf

variable {X : ℕ →. ℕ}

/-- **`β < ω₁^X → ω · β < ω₁^X`**, from representability. -/
theorem omega0_mul_lt {β : Ordinal.{0}} (h : β < omegaOneOf X) : ω * β < omegaOneOf X :=
  lt_of_mem (RecOrdinals.omega0_mul_mem (lt_iff.1 h))

end omegaOneOf
