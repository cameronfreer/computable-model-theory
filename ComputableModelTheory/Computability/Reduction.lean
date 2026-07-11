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
encoding of `decide (p a)`, and it diverges on non-codes. Partiality keeps the oracle
itself recursive in any oracle set that computes `p`, which drives transitivity of
`PredTuringReducible`.

Because it diverges off valid codes, this is not literally the conventional total
characteristic oracle; `predOracleTotal` is, and the two are interchangeable as oracle
sets (`computablePredIn_predOracle_iff_total`), so either may be used before degree
theory. -/
def predOracle (p : α → Prop) [DecidablePred p] : ℕ →. ℕ :=
  fun n ↦ (decode (α := α) n : Part α).map fun a ↦ encode (decide (p a))

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

/-- Any oracle set that computes a decidable predicate computes its characteristic
oracle. -/
theorem recursiveIn_predOracle {p : α → Prop} [DecidablePred p]
    (hp : ComputablePredIn O p) : RecursiveIn O (predOracle p) :=
  RecursiveIn.map (ComputableIn.ofOption Computable.decode.computableIn)
    (((ComputableIn.encode.comp hp.decide).comp ComputableIn.snd).to₂)

/-- The conventional total characteristic oracle of a decidable predicate: on the code
of `a` it returns the encoding of `decide (p a)`, and it returns `encode false` off
valid codes. -/
def predOracleTotal (p : α → Prop) [DecidablePred p] : ℕ →. ℕ :=
  fun n ↦ Part.some (Option.casesOn (motive := fun _ ↦ ℕ) (decode (α := α) n)
    (encode false) fun a ↦ encode (decide (p a)))

/-- The total characteristic oracle on valid codes. -/
theorem predOracleTotal_encode (p : α → Prop) [DecidablePred p] (a : α) :
    predOracleTotal p (encode a) = Part.some (encode (decide (p a))) := by
  rw [predOracleTotal, encodek]

/-- The total characteristic oracle off valid codes. -/
theorem predOracleTotal_of_decode_none (p : α → Prop) [DecidablePred p] {n : ℕ}
    (h : decode (α := α) n = Option.none) :
    predOracleTotal p n = Part.some (encode false) := by
  rw [predOracleTotal, h]

/-- The partial characteristic oracle computes the total one: off valid codes the
default is produced without a query. -/
theorem recursiveIn_predOracleTotal_of_predOracle (p : α → Prop) [DecidablePred p] :
    RecursiveIn {predOracle p} (predOracleTotal p) := by
  have horacle : RecursiveIn {predOracle p} (predOracle p) :=
    RecursiveIn.iff_nat.2 (Nat.RecursiveIn.oracle _ rfl)
  have h : RecursiveIn {predOracle p} fun n : ℕ ↦
      Nat.casesOn (motive := fun _ ↦ Part ℕ) (encode (decode (α := α) n))
        (Part.some (encode false)) fun _ ↦ predOracle p n :=
    RecursiveIn.nat_casesOn_right
      ((Computable.encode.comp Computable.decode).computableIn)
      (ComputableIn.const (encode false))
      ((horacle.comp ComputableIn.fst).to₂)
  refine h.of_eq fun n ↦ ?_
  rcases hd : decode (α := α) n with - | a
  · rw [show encode (none : Option α) = 0 from rfl, predOracleTotal_of_decode_none p hd]
    rfl
  · rw [show encode (Option.some a) = encode a + 1 from rfl]
    show predOracle p n = predOracleTotal p n
    rw [predOracle, predOracleTotal, hd]
    simp

/-- The total characteristic oracle computes the partial one: the query is guarded by
the decoding. -/
theorem recursiveIn_predOracle_of_predOracleTotal (p : α → Prop) [DecidablePred p] :
    RecursiveIn {predOracleTotal p} (predOracle p) := by
  have horacle : RecursiveIn {predOracleTotal p} (predOracleTotal p) :=
    RecursiveIn.iff_nat.2 (Nat.RecursiveIn.oracle _ rfl)
  have h : RecursiveIn {predOracleTotal p} fun n : ℕ ↦
      ((decode (α := α) n : Part α)).bind fun _ ↦ predOracleTotal p n :=
    RecursiveIn.bind (ComputableIn.ofOption Computable.decode.computableIn)
      ((horacle.comp ComputableIn.fst).to₂)
  refine h.of_eq fun n ↦ ?_
  rcases hd : decode (α := α) n with - | a
  · rw [predOracle, hd]
    exact Part.ext fun b ↦ by simp
  · rw [predOracle, predOracleTotal, hd]
    simp

/-- The partial and total characteristic oracles are interchangeable as oracle sets:
computability of any predicate transports both ways. -/
theorem computablePredIn_predOracle_iff_total (p : α → Prop) [DecidablePred p]
    {q : β → Prop} :
    ComputablePredIn {predOracle p} q ↔ ComputablePredIn {predOracleTotal p} q := by
  constructor
  · refine computablePredIn_of_oracle_transport fun g hg ↦ ?_
    rw [Set.mem_singleton_iff.1 hg]
    exact recursiveIn_predOracle_of_predOracleTotal p
  · refine computablePredIn_of_oracle_transport fun g hg ↦ ?_
    rw [Set.mem_singleton_iff.1 hg]
    exact recursiveIn_predOracleTotal_of_predOracle p

/-- A decidable predicate is computable from its own total characteristic oracle. -/
theorem computablePredIn_predOracleTotal_self (p : α → Prop) [DecidablePred p] :
    ComputablePredIn {predOracleTotal p} p :=
  (computablePredIn_predOracle_iff_total p).1 (computablePredIn_predOracle_self p)

set_option linter.unusedDecidableInType false in
/-- Reflexivity of predicate Turing reducibility. The `Decidable` hypothesis supplies the
existential witness in `PredTuringReducible` and keeps the assumption explicit. -/
theorem PredTuringReducible.refl (p : α → Prop) [DecidablePred p] :
    PredTuringReducible p p :=
  ⟨inferInstance, computablePredIn_predOracle_self p⟩

/-- Transitivity of predicate Turing reducibility: an oracle computation relative to `q`
composes with an oracle computation of `q` relative to `r`, by transporting along the
fact that the `r`-oracle computes the `q`-oracle. -/
theorem PredTuringReducible.trans {γ : Type*} [Primcodable γ] {p : α → Prop}
    {q : β → Prop} {r : γ → Prop} :
    PredTuringReducible p q → PredTuringReducible q r → PredTuringReducible p r
  | ⟨_, hpq⟩, ⟨Dr, hqr⟩ =>
    ⟨Dr, computablePredIn_of_oracle_transport
      (fun g hg ↦ by
        rw [Set.mem_singleton_iff] at hg
        subst hg
        exact recursiveIn_predOracle hqr)
      hpq⟩

end
