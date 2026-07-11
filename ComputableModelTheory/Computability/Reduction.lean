/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.OraclePred

/-!
# Lightweight reductions and oracle transport

This file provides just enough reducibility API to state that a predicate or function is
computable from a given oracle (for example, embedding information), without formalizing
Turing degrees as quotients: the characteristic oracle `predOracle` of a decidable
predicate, predicate Turing reducibility `PredTuringReducible`, and transport lemmas
moving computability and enumerability along oracle-set equality, inclusion, and
relative computation of oracles (`RecursiveIn.subst`).

No Turing jumps and no degree quotients; those come later, once concrete statements
need them.
-/

open Encodable Part

section

variable {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]
variable {O O₁ O₂ : Set (ℕ →. ℕ)} {p q : α → Prop} {f : α → σ}

/-- The characteristic oracle of a decidable predicate: on the code of `a` it returns the
encoding of `decide (p a)`; on non-codes it returns `0`. It is total. -/
def predOracle (p : α → Prop) [DecidablePred p] : ℕ →. ℕ :=
  fun n ↦ Part.some (encode ((decode (α := α) n).elim false fun a ↦ decide (p a)))

/-- Turing reducibility of predicates, without Turing degrees: `p` is computable relative
to the characteristic oracle of `q` (for some decidability witness for `q`). -/
def PredTuringReducible {α β : Type*} [Primcodable α] [Primcodable β]
    (p : α → Prop) (q : β → Prop) : Prop :=
  ∃ _ : DecidablePred q, ComputablePredIn {predOracle q} p

/-- Oracle transport for functions: computability relative to `O₁` transports along any
`O₂` that computes every oracle in `O₁`. -/
theorem ComputableIn.of_oracle_transport (hO : ∀ g ∈ O₁, RecursiveIn O₂ g)
    (hf : ComputableIn O₁ f) : ComputableIn O₂ f :=
  RecursiveIn.subst hf hO

/-- Oracle transport for partial functions. -/
theorem RecursiveIn.of_oracle_transport {f : α →. σ} (hO : ∀ g ∈ O₁, RecursiveIn O₂ g)
    (hf : RecursiveIn O₁ f) : RecursiveIn O₂ f :=
  RecursiveIn.subst hf hO

/-- Oracle transport for computable predicates. -/
theorem computablePredIn_of_oracle_transport (hO : ∀ g ∈ O₁, RecursiveIn O₂ g) :
    ComputablePredIn O₁ p → ComputablePredIn O₂ p
  | ⟨D, h⟩ => ⟨D, RecursiveIn.subst h hO⟩

/-- Oracle transport for r.e. predicates. -/
theorem rePredIn_of_oracle_transport (hO : ∀ g ∈ O₁, RecursiveIn O₂ g)
    (hp : REPredIn O₁ p) : REPredIn O₂ p :=
  RecursiveIn.subst hp hO

/-- Computability is invariant under equality of oracle sets. -/
theorem computablePredIn_of_oracle_eq (h : O₁ = O₂) (hp : ComputablePredIn O₁ p) :
    ComputablePredIn O₂ p :=
  h ▸ hp

/-- Computability transports along oracle-set inclusion; alias for `ComputablePredIn.mono`
in the transport vocabulary. -/
theorem computablePredIn_of_subset_oracle (h : O₁ ⊆ O₂) (hp : ComputablePredIn O₁ p) :
    ComputablePredIn O₂ p :=
  hp.mono h

/-- A decidable predicate is computable relative to its own characteristic oracle. -/
theorem computablePredIn_predOracle_self (p : α → Prop) [DecidablePred p] :
    ComputablePredIn {predOracle p} p := by
  refine ⟨inferInstance, ?_⟩
  have horacle : RecursiveIn {predOracle p} (predOracle p) :=
    RecursiveIn.iff_nat.2 (Nat.RecursiveIn.oracle _ rfl)
  have h1 : RecursiveIn {predOracle p} fun a : α ↦ predOracle p (encode a) :=
    RecursiveIn.comp horacle ComputableIn.encode
  have h2 : RecursiveIn {predOracle p} fun a : α ↦ Part.some (encode (decide (p a))) :=
    h1.of_eq fun a ↦ by simp [predOracle, encodek]
  exact ComputableIn.encode_iff.1 h2

set_option linter.unusedDecidableInType false in
/-- Reflexivity of predicate Turing reducibility. The `Decidable` hypothesis supplies the
existential witness in `PredTuringReducible` and keeps the assumption explicit. -/
theorem PredTuringReducible.refl (p : α → Prop) [DecidablePred p] :
    PredTuringReducible p p :=
  ⟨inferInstance, computablePredIn_predOracle_self p⟩

end
