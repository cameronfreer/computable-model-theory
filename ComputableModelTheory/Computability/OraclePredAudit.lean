/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.OraclePred
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for oracle predicates

Named acceptance tests for `ComputablePredIn`/`REPredIn` and the typed combinators, each
checked by `#assert_standard_axioms`, which fails elaboration — and therefore CI — if a
declaration depends on any axiom other than `propext`, `Classical.choice`, `Quot.sound`.
This module is deliberately not imported by the library's root spine; CI checks it
explicitly with

```
lake env lean ComputableModelTheory/Computability/OraclePredAudit.lean
```
-/

section

variable {α β : Type*} [Primcodable α] [Primcodable β] {O O₁ O₂ : Set (ℕ →. ℕ)}
  {p q : α → Prop} {r : α → β → Prop}

/-- Boolean closure: the roadmap acceptance gate `hp.and hq.not`. -/
theorem test_and_not (hp : ComputablePredIn O p) (hq : ComputablePredIn O q) :
    ComputablePredIn O fun a ↦ p a ∧ ¬q a :=
  hp.and hq.not

/-- Boolean closure: disjunction. -/
theorem test_or (hp : ComputablePredIn O p) (hq : ComputablePredIn O q) :
    ComputablePredIn O fun a ↦ p a ∨ q a :=
  hp.or hq

/-- Boolean closure: implication. -/
theorem test_imp (hp : ComputablePredIn O p) (hq : ComputablePredIn O q) :
    ComputablePredIn O fun a ↦ p a → q a :=
  hp.imp hq

/-- Boolean closure: bi-implication. -/
theorem test_iff (hp : ComputablePredIn O p) (hq : ComputablePredIn O q) :
    ComputablePredIn O fun a ↦ (p a ↔ q a) :=
  hp.iff hq

/-- Oracle-set monotonicity. -/
theorem test_mono (hsub : O₁ ⊆ O₂) (hp : ComputablePredIn O₁ p) : ComputablePredIn O₂ p :=
  hp.mono hsub

/-- Existential quantification over `Fin n`. -/
theorem test_exists_fin {n : ℕ} {p : α → Fin n → Prop}
    (hp : ComputablePredIn O fun x : α × Fin n ↦ p x.1 x.2) :
    ComputablePredIn O fun a ↦ ∃ i, p a i :=
  hp.exists_fin

/-- Universal quantification over `Fin n`. -/
theorem test_forall_fin {n : ℕ} {p : α → Fin n → Prop}
    (hp : ComputablePredIn O fun x : α × Fin n ↦ p x.1 x.2) :
    ComputablePredIn O fun a ↦ ∀ i, p a i :=
  hp.forall_fin

/-- Bounded existential quantification over a fixed finset. -/
theorem test_exists_finset (s : Finset β)
    (hp : ComputablePredIn O fun x : α × β ↦ r x.1 x.2) :
    ComputablePredIn O fun a ↦ ∃ b ∈ s, r a b :=
  ComputablePredIn.exists_finset s hp

/-- Bounded universal quantification over a fixed finset. -/
theorem test_forall_finset (s : Finset β)
    (hp : ComputablePredIn O fun x : α × β ↦ r x.1 x.2) :
    ComputablePredIn O fun a ↦ ∀ b ∈ s, r a b :=
  ComputablePredIn.forall_finset s hp

/-- The binary relation wrappers are definitional repackagings of the pair predicates. -/
theorem test_computableRelIn_iff :
    ComputableRelIn O r ↔ ComputablePredIn O fun x : α × β ↦ r x.1 x.2 :=
  Iff.rfl

/-- The binary r.e. relation wrapper is a definitional repackaging of the pair predicate. -/
theorem test_reRelIn_iff :
    RERelIn O r ↔ REPredIn O fun x : α × β ↦ r x.1 x.2 :=
  Iff.rfl

/-- Computable-to-r.e. conversion. -/
theorem test_to_rePredIn (hp : ComputablePredIn O p) : REPredIn O p :=
  hp.to_rePredIn

/-- A natural-number existential over a computable predicate is r.e. -/
theorem test_exists_nat {p : α → ℕ → Prop}
    (hp : ComputablePredIn O fun x : α × ℕ ↦ p x.1 x.2) :
    REPredIn O fun a ↦ ∃ n, p a n :=
  REPredIn.exists_nat_of_computablePredIn hp

/-- Mixed conjunction, computable on the left. -/
theorem test_and_computable_left (hp : ComputablePredIn O p) (hq : REPredIn O q) :
    REPredIn O fun a ↦ p a ∧ q a :=
  REPredIn.and_computable_left hp hq

/-- Mixed conjunction, computable on the right. -/
theorem test_and_computable_right (hp : REPredIn O p) (hq : ComputablePredIn O q) :
    REPredIn O fun a ↦ p a ∧ q a :=
  REPredIn.and_computable_right hp hq

/-- Boolean conditionals of oracle-computable functions. -/
theorem test_cond {c : α → Bool} {f g : α → β} (hc : ComputableIn O c)
    (hf : ComputableIn O f) (hg : ComputableIn O g) :
    ComputableIn O fun a ↦ bif c a then f a else g a :=
  ComputableIn.cond hc hf hg

/-- μ-search over a total predicate, exactly the plan-contract statement. -/
theorem test_rfind_total {f : α → ℕ → Bool} (hf : ComputableIn₂ O f) :
    RecursiveIn O fun a ↦ Nat.rfind fun n ↦ Part.some (f a n) :=
  RecursiveIn.rfind_total hf

/-- μ-search over a general partial `Bool`-valued predicate. -/
theorem test_rfind {p : α → ℕ →. Bool} (hp : RecursiveIn₂ O p) :
    RecursiveIn O fun a ↦ Nat.rfind (p a) :=
  RecursiveIn.rfind hp

end

/-- Semantic gate for μ-search: the search halts **exactly** when a witness exists,
in both directions. -/
theorem test_rfind_dom_iff {α : Type*} {f : α → ℕ → Bool} {a : α} :
    (Nat.rfind fun n ↦ Part.some (f a n)).Dom ↔ ∃ n, f a n = true :=
  Nat.rfind_some_dom_iff

/-- Semantic gate for μ-search: the found index satisfies the predicate. -/
theorem test_rfind_spec {α : Type*} {f : α → ℕ → Bool} {a : α} {n : ℕ}
    (h : n ∈ Nat.rfind fun k ↦ Part.some (f a k)) : f a n = true :=
  Nat.rfind_some_spec h

#assert_standard_axioms test_and_not
#assert_standard_axioms test_or
#assert_standard_axioms test_imp
#assert_standard_axioms test_iff
#assert_standard_axioms test_mono
#assert_standard_axioms test_exists_fin
#assert_standard_axioms test_forall_fin
#assert_standard_axioms test_exists_finset
#assert_standard_axioms test_forall_finset
#assert_standard_axioms test_computableRelIn_iff
#assert_standard_axioms test_reRelIn_iff
#assert_standard_axioms test_to_rePredIn
#assert_standard_axioms test_exists_nat
#assert_standard_axioms test_and_computable_left
#assert_standard_axioms test_and_computable_right
#assert_standard_axioms test_cond
#assert_standard_axioms test_rfind_total
#assert_standard_axioms test_rfind
#assert_standard_axioms test_rfind_dom_iff
#assert_standard_axioms test_rfind_spec
