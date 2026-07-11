/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.RecursiveIn
import Mathlib.Computability.Partrec
import Mathlib.Computability.RE

/-!
# Relative computable and r.e. predicates

This file defines `ComputablePredIn` and `REPredIn`, the oracle-relative analogues of
mathlib's `ComputablePred` and `REPred`, together with their closure lemmas (Boolean
operations, finite quantifiers, and the computable-to-r.e. bridge). Oracles are sets
`O : Set (ℕ →. ℕ)`, matching mathlib's `RecursiveIn`/`ComputableIn` layer.
-/

open Encodable Part

/-- A predicate is computable in `O` if it is decidable and its indicator function is
computable in `O`. -/
def ComputablePredIn (O : Set (ℕ →. ℕ)) {α : Type*} [Primcodable α] (p : α → Prop) : Prop :=
  ∃ _ : DecidablePred p, ComputableIn O fun a ↦ decide (p a)

/-- A predicate is recursively enumerable in `O` if it is the domain of a partial function
recursive in `O`. -/
def REPredIn (O : Set (ℕ →. ℕ)) {α : Type*} [Primcodable α] (p : α → Prop) : Prop :=
  RecursiveIn O fun a ↦ Part.assert (p a) fun _ ↦ Part.some ()

/-- A binary relation is computable in `O` if the corresponding predicate on pairs is. -/
def ComputableRelIn (O : Set (ℕ →. ℕ)) {α β : Type*} [Primcodable α] [Primcodable β]
    (p : α → β → Prop) : Prop :=
  ComputablePredIn O fun x : α × β ↦ p x.1 x.2

/-- A binary relation is recursively enumerable in `O` if the corresponding predicate on
pairs is. -/
def RERelIn (O : Set (ℕ →. ℕ)) {α β : Type*} [Primcodable α] [Primcodable β]
    (p : α → β → Prop) : Prop :=
  REPredIn O fun x : α × β ↦ p x.1 x.2

section

variable {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]
variable {O O₁ O₂ : Set (ℕ →. ℕ)} {p q : α → Prop}

/-- The indicator function of an oracle-computable predicate is oracle-computable, for any
ambient decidability instance. -/
protected theorem ComputablePredIn.decide [DecidablePred p] (h : ComputablePredIn O p) :
    ComputableIn O fun a ↦ decide (p a) := by
  convert! h.choose_spec

/-- A decidable predicate with oracle-computable indicator function is oracle-computable. -/
theorem ComputableIn.computablePredIn [DecidablePred p]
    (h : ComputableIn O fun a ↦ decide (p a)) : ComputablePredIn O p :=
  ⟨inferInstance, h⟩

/-- For decidable predicates, oracle computability of the predicate and of its indicator
function coincide. -/
theorem computablePredIn_iff_computableIn_decide [DecidablePred p] :
    ComputablePredIn O p ↔ ComputableIn O fun a ↦ decide (p a) :=
  ⟨ComputablePredIn.decide, ComputableIn.computablePredIn⟩

/-- The domain of an oracle-partial-recursive function is r.e. in the same oracles. -/
theorem RecursiveIn.dom_rePredIn {f : α →. σ} (hf : RecursiveIn O f) :
    REPredIn O fun a ↦ (f a).Dom :=
  (RecursiveIn.map hf ((ComputableIn.const ()).to₂)).of_eq fun n ↦
    Part.ext fun _ ↦ by simp [Part.dom_iff_mem]

/-- Predicates extensionally equivalent to an oracle-computable predicate are
oracle-computable. -/
theorem ComputablePredIn.of_eq (hp : ComputablePredIn O p) (H : ∀ a, p a ↔ q a) :
    ComputablePredIn O q :=
  (funext fun a ↦ propext (H a) : p = q) ▸ hp

/-- Oracle-set monotonicity: a predicate computable in `O₁` is computable in any `O₂ ⊇ O₁`. -/
theorem ComputablePredIn.mono (hO : O₁ ⊆ O₂) : ComputablePredIn O₁ p → ComputablePredIn O₂ p
  | ⟨D, h⟩ => ⟨D, RecursiveIn.mono hO h⟩

/-- Precomposition of an oracle-computable predicate with an oracle-computable function. -/
protected theorem ComputablePredIn.comp {p : β → Prop} {f : α → β} (hp : ComputablePredIn O p)
    (hf : ComputableIn O f) : ComputablePredIn O fun a ↦ p (f a) :=
  let ⟨D, h⟩ := hp
  ⟨fun a ↦ D (f a), h.comp hf⟩

/-- Predicates extensionally equivalent to an oracle-r.e. predicate are oracle-r.e. -/
theorem REPredIn.of_eq (hp : REPredIn O p) (H : ∀ a, p a ↔ q a) : REPredIn O q :=
  (funext fun a ↦ propext (H a) : p = q) ▸ hp

/-- Oracle-set monotonicity: a predicate r.e. in `O₁` is r.e. in any `O₂ ⊇ O₁`. -/
theorem REPredIn.mono (hO : O₁ ⊆ O₂) (hp : REPredIn O₁ p) : REPredIn O₂ p :=
  RecursiveIn.mono hO hp

/-! ### Boolean closure -/

namespace ComputablePredIn

/-- Constant predicates are computable in any oracle set. -/
theorem const (b : Prop) [Decidable b] : ComputablePredIn O fun _ : α ↦ b :=
  ⟨fun _ ↦ ‹Decidable b›, ComputableIn.const (decide b)⟩

/-- Oracle-computable predicates are closed under negation. -/
protected theorem not : ComputablePredIn O p → ComputablePredIn O fun a ↦ ¬p a
  | ⟨_, hp⟩ =>
    ComputableIn.computablePredIn <|
      (Primrec.not.to_comp.computableIn.comp hp).of_eq fun a ↦ by simp

/-- Oracle-computable predicates are closed under conjunction. -/
protected theorem and : ComputablePredIn O p → ComputablePredIn O q →
    ComputablePredIn O fun a ↦ p a ∧ q a
  | ⟨_, hp⟩, ⟨_, hq⟩ =>
    ComputableIn.computablePredIn <|
      (Primrec.and.to_comp.computableIn₂.comp hp hq).of_eq fun a ↦ by simp

/-- Oracle-computable predicates are closed under disjunction. -/
protected theorem or : ComputablePredIn O p → ComputablePredIn O q →
    ComputablePredIn O fun a ↦ p a ∨ q a
  | ⟨_, hp⟩, ⟨_, hq⟩ =>
    ComputableIn.computablePredIn <|
      (Primrec.or.to_comp.computableIn₂.comp hp hq).of_eq fun a ↦ by simp

/-- Oracle-computable predicates are closed under implication. -/
protected theorem imp (hp : ComputablePredIn O p) (hq : ComputablePredIn O q) :
    ComputablePredIn O fun a ↦ p a → q a :=
  (hp.not.or hq).of_eq fun _ ↦ imp_iff_not_or.symm

/-- Oracle-computable predicates are closed under bi-implication. -/
protected theorem iff (hp : ComputablePredIn O p) (hq : ComputablePredIn O q) :
    ComputablePredIn O fun a ↦ (p a ↔ q a) :=
  ((hp.imp hq).and (hq.imp hp)).of_eq fun _ ↦ iff_iff_implies_and_implies.symm

end ComputablePredIn

end
