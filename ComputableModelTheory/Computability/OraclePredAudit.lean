/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.OraclePred

/-!
# Audit module for oracle predicates

Named acceptance tests for `ComputablePredIn`/`REPredIn` and the μ-search combinators,
each followed by an explicit `#print axioms` command. This module is deliberately not
imported by the library's root spine; it is checked explicitly with

```
lake env lean ComputableModelTheory/Computability/OraclePredAudit.lean
```

Expected axioms for every test: at most `propext`, `Classical.choice`, `Quot.sound`.
-/

section

variable {α : Type*} [Primcodable α] {O O₁ O₂ : Set (ℕ →. ℕ)} {p q : α → Prop}

/-- Boolean closure: the roadmap acceptance gate `hp.and hq.not`. -/
theorem test_and_not (hp : ComputablePredIn O p) (hq : ComputablePredIn O q) :
    ComputablePredIn O fun a ↦ p a ∧ ¬q a :=
  hp.and hq.not

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

end

/-- Semantic gate for μ-search: the search halts exactly on a witness. -/
theorem test_rfind_dom {α : Type*} {f : α → ℕ → Bool} {a : α} (h : ∃ n, f a n = true) :
    (Nat.rfind fun n ↦ Part.some (f a n)).Dom :=
  RecursiveIn.rfind_dom_iff.2 h

/-- Semantic gate for μ-search: the found index satisfies the predicate. -/
theorem test_rfind_spec {α : Type*} {f : α → ℕ → Bool} {a : α} {n : ℕ}
    (h : n ∈ Nat.rfind fun k ↦ Part.some (f a k)) : f a n = true :=
  RecursiveIn.rfind_spec h

#print axioms test_and_not
#print axioms test_mono
#print axioms test_exists_fin
#print axioms test_forall_fin
#print axioms test_to_rePredIn
#print axioms test_exists_nat
#print axioms test_and_computable_left
#print axioms test_and_computable_right
#print axioms test_rfind_dom
#print axioms test_rfind_spec
