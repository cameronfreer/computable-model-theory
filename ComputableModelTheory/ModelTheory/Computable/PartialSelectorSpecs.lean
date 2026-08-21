/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PartialCJEP
import ComputableModelTheory.ModelTheory.Computable.PartialMemberEmbedding

/-!
# Selector-facing forms of the effective properties

`PartialCJEPIn` and `MappedPartialCHPIn` state their soundness clauses **in coordinates**: a length
equation together with a family of equations placing the images of the recorded generators. That is
the right shape for the *definitions* — it is what the paper asserts, and it is checkable against
the paper line by line.

It is the wrong shape for a *consumer*. Every construction downstream runs `applyPotentialPart` on
the answer, so what it wants is potential embedding data together with a realizer:
`K.PartialIsEmbedding (ofTriple (…))`. `partialIsEmbedding_ofTriple` says the repackaging is free —
`PartialRealizes` at `ofTriple (c, e, s)` unfolds to exactly the length-and-coordinate data, since
all three `ofTriple` projections are `rfl` — so naming the consumer-facing form loses nothing and
keeps coordinate bookkeeping out of every producer.

`JointSpec` and `MappedCHPSpec` are those two forms, with their extraction theorems. They are
collected here rather than left with any one consumer: the schedule layer, both covers of
Theorem 2.10, and the oracle-rebase theorem all take them, and none of those files owns them.

**Rebasing to a stronger oracle changes nothing here.** All four `mono_*` bridges are `Iff.rfl`:
these properties quantify only over `gens`, `memberAt`, `domainAt` and their induced subtype
structures, every one of which `PartialAgeIn.mono` carries definitionally. That is the precise
sense in which the selector oracle is *evidence* about a family and not part of the family. If a
future refactor breaks one of these `rfl`s, it has changed what a representation is, and deserves
scrutiny rather than a routine transport proof.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

namespace PartialAgeIn

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-! ### The joint-embedding answer -/

/-- Both legs of a joint-embedding selector are actual, at every pair of indices. -/
def JointSpec (K : PartialAgeIn O L) (sel : ℕ → ℕ → PartialJointEmbeddingData) : Prop :=
  ∀ i j : ℕ,
    K.PartialIsEmbedding
        (PotentialEmbeddingData.ofTriple (i, (sel i j).apexIdx, (sel i j).leftImage)) ∧
      K.PartialIsEmbedding
        (PotentialEmbeddingData.ofTriple (j, (sel i j).apexIdx, (sel i j).rightImage))

/-- CJEP delivers exactly that, with a computable selector. -/
theorem PartialCJEPIn.exists_jointSpec {K : PartialAgeIn O L} (h : K.PartialCJEPIn E) :
    ∃ sel : ℕ → ℕ → PartialJointEmbeddingData,
      ComputableIn E (fun p : ℕ × ℕ ↦ sel p.1 p.2) ∧ K.JointSpec sel := by
  obtain ⟨sel, hsel, hspec⟩ := h
  refine ⟨sel, hsel, fun i j ↦ ?_⟩
  obtain ⟨⟨hlen, Fi, hFi⟩, ⟨hlen', Fj, hFj⟩⟩ := hspec i j
  exact ⟨⟨Fi, hlen, hFi⟩, ⟨Fj, hlen', hFj⟩⟩

/-! ### The hereditary answer -/

/-- **What a consumer of the hereditary property actually needs**, as reusable data: for every valid
query, the selected member's index together with potential embedding data that is *actual*. -/
def MappedCHPSpec (K : PartialAgeIn O L) (sel : ℕ → List ℕ →. ℕ) : Prop :=
  ∀ (e : ℕ) (s : List ℕ), (∀ x ∈ s, x ∈ K.domainAt e) →
    ∃ c ∈ sel e s, K.PartialIsEmbedding (PotentialEmbeddingData.ofTriple (c, e, s))

/-- CHP delivers exactly that, with a computable selector. The extraction is
`partialIsEmbedding_ofTriple` applied to the contract's own witnesses — no coordinate bookkeeping
crosses this boundary. -/
theorem MappedPartialCHPIn.exists_chpSpec {K : PartialAgeIn O L}
    (h : MappedPartialCHPIn E K) :
    ∃ sel : ℕ → List ℕ →. ℕ,
      RecursiveIn E (fun p : ℕ × List ℕ ↦ sel p.1 p.2) ∧ K.MappedCHPSpec sel := by
  obtain ⟨sel, hsel, hspec⟩ := h
  refine ⟨sel, hsel, fun e s hs ↦ ?_⟩
  obtain ⟨c, hc, hlen, F, hF⟩ := hspec e s hs
  exact ⟨c, hc, partialIsEmbedding_ofTriple hlen F hF⟩

/-! ### Rebasing preserves all four, on the nose

Each bridge is `Iff.rfl`. Both properties, and both of their selector-facing forms, quantify only
over data `mono` carries definitionally — so there is no transport step to write, and `K`'s
effective properties at `E` *are* the rebased family's. -/

variable {K : PartialAgeIn O L}

@[simp] theorem mono_partialCJEPIn (hOE : O ⊆ E) {E' : Set (ℕ →. ℕ)} :
    (K.mono hOE).PartialCJEPIn E' ↔ K.PartialCJEPIn E' :=
  Iff.rfl

@[simp] theorem mono_mappedPartialCHPIn (hOE : O ⊆ E) {E' : Set (ℕ →. ℕ)} :
    MappedPartialCHPIn E' (K.mono hOE) ↔ MappedPartialCHPIn E' K :=
  Iff.rfl

@[simp] theorem mono_jointSpec (hOE : O ⊆ E) {sel : ℕ → ℕ → PartialJointEmbeddingData} :
    (K.mono hOE).JointSpec sel ↔ K.JointSpec sel :=
  Iff.rfl

@[simp] theorem mono_mappedCHPSpec (hOE : O ⊆ E) {sel : ℕ → List ℕ →. ℕ} :
    (K.mono hOE).MappedCHPSpec sel ↔ K.MappedCHPSpec sel :=
  Iff.rfl

end PartialAgeIn

end FirstOrder.Language
