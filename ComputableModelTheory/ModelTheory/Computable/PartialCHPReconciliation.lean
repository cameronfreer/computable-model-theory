/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.EffectiveWitnesses
import ComputableModelTheory.ModelTheory.Computable.PartialTheorem28

/-!
# The all-ℕ CHP adapter

The reconciliation of the paper-facing selector contract with the all-ℕ effective HP witness
interface:

```
Nonempty (HPWitnessIn E K)  ↔  MappedPartialCHPIn E K.toPartialAge
```

for an **arbitrary** witness oracle `E`. No `O ⊆ E` is needed in either direction: both
interfaces store an `E`-effective selector, and both soundness clauses are semantic and only
mention the presentation. The presentation oracle enters nowhere below.

`HPWitnessIn` is a structure and `MappedPartialCHPIn` a proposition, so the transformations
are stated separately and the logical equivalence is the `Nonempty` form.

Nothing here rebuilds the closure equivalence or re-derives a carrier change:

* `PotentialEmbeddingData.toEmbedding` already realizes an actual potential embedding, with
  `toEmbedding_apply_gens` giving the generator coordinates;
* `isEmbedding_of_embedding_extending_tuple` already runs the converse;
* `ComputableAgeIn.embeddingToPartial` / `embeddingOfPartial` already conjugate between the
  stored structures and the member carrier subtypes.

Two conventions have to be matched, and both are confined to this file's first section:
`WellFormed` measures the range tuple against the generators while `MappedPartialCHPIn`
measures the generators against the queried tuple, so `Fin.cast` appears only in
`wellFormed_iff_gens_length` and `toEmbedding_apply_gens_get`.

The effectivity gap is the expected one: `HPWitnessIn`'s selector is total and computable,
`MappedPartialCHPIn`'s is partial. On all-ℕ carriers every tuple is drawn from every member,
so the soundness hypothesis is vacuous, the partial selector is everywhere defined, and
`RecursiveIn.computableIn_get` totalizes it.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

variable {K : ComputableAgeIn O L}

namespace PartialAgeIn

/-! ### The two length conventions -/

/-- `WellFormed` and `MappedPartialCHPIn`'s length clause are each other's `symm`. -/
theorem wellFormed_iff_gens_length {c e : ℕ} {s : Tuple ℕ} :
    (⟨c, e, s⟩ : PotentialEmbeddingData).WellFormed K ↔ (K.gens c).length = s.length :=
  eq_comm

/-- The generator coordinates of the realized embedding, in the form `MappedPartialCHPIn`
asks for. The only other place `Fin.cast` appears. -/
theorem toEmbedding_apply_gens_get {c e : ℕ} {s : Tuple ℕ}
    (h : (⟨c, e, s⟩ : PotentialEmbeddingData).WellFormed K)
    (hAE : @AtomicEquivalent L ℕ ℕ (K.structureAt c) (K.structureAt e) _
      (K.gens c).view ((⟨c, e, s⟩ : PotentialEmbeddingData).targetView h))
    (k : Fin (K.gens c).length) :
    PotentialEmbeddingData.toEmbedding h hAE ((K.gens c).get k) =
      s.get (Fin.cast (wellFormed_iff_gens_length.1 h) k) :=
  PotentialEmbeddingData.toEmbedding_apply_gens h hAE k

/-! ### Paper-facing selector → effective HP witness -/

/-- A paper-facing selector for the embedded all-ℕ family is an effective HP witness, at the
**same** witness oracle: on all-ℕ carriers the soundness hypothesis is vacuous, so the
selector is everywhere defined and totalizes, and the supplied member embedding conjugates
back to an embedding of the stored structures extending the tuple assignment. -/
theorem MappedPartialCHPIn.nonempty_hpWitnessIn
    (h : MappedPartialCHPIn E K.toPartialAge) : Nonempty (HPWitnessIn E K) := by
  obtain ⟨sel, hsel, hspec⟩ := h
  have htot : ∀ p : ℕ × Tuple ℕ, (sel p.1 p.2).Dom := fun p ↦
    (hspec p.1 p.2 fun x _ ↦ K.mem_toPartialAge_memberAt_domain p.1 x).choose_spec.1.fst
  refine ⟨{ select := fun p ↦ (sel p.1 p.2).get (htot p)
            computable := hsel.computableIn_get htot
            sound := fun i a ↦ ?_ }⟩
  obtain ⟨c, hc, hlen, F, hF⟩ :=
    hspec i a fun x _ ↦ K.mem_toPartialAge_memberAt_domain i x
  have hcget : (sel i a).get (htot (i, a)) = c := Part.get_eq_of_mem hc _
  rw [hcget]
  refine PotentialEmbeddingData.isEmbedding_of_embedding_extending_tuple
    (wellFormed_iff_gens_length.2 hlen) (K.embeddingOfPartial F) fun k ↦ ?_
  exact hF k

end PartialAgeIn

/-! ### Effective HP witness → paper-facing selector -/

open PartialAgeIn in
/-- An all-ℕ effective HP witness is a paper-facing selector for the family it embeds to, at
the **same** witness oracle. -/
theorem HPWitnessIn.mappedPartialCHPIn (W : HPWitnessIn E K) :
    PartialAgeIn.MappedPartialCHPIn E K.toPartialAge := by
  refine ⟨fun e s ↦ Part.some (W.select (e, s)),
    (W.computable.of_eq fun _ ↦ rfl :
      ComputableIn E fun p : ℕ × List ℕ ↦ W.select (p.1, p.2)),
    fun e s _ ↦ ?_⟩
  obtain ⟨h, hAE⟩ := W.sound e s
  refine ⟨W.select (e, s), Part.mem_some _, wellFormed_iff_gens_length.1 h,
    K.embeddingToPartial (PotentialEmbeddingData.toEmbedding h hAE), fun k ↦ ?_⟩
  rw [K.embeddingToPartial_coe]
  exact toEmbedding_apply_gens_get h hAE k

/-! ### The equivalence -/

/-- **The all-ℕ CHP reconciliation.** For an arbitrary witness oracle `E`, an effective HP
witness for an all-ℕ computable age is exactly a paper-facing selector for the family it
embeds to. No `O ⊆ E`: the presentation oracle enters neither direction. -/
theorem nonempty_hpWitnessIn_iff_mappedPartialCHPIn (K : ComputableAgeIn O L)
    (E : Set (ℕ →. ℕ)) :
    Nonempty (HPWitnessIn E K) ↔ PartialAgeIn.MappedPartialCHPIn E K.toPartialAge :=
  ⟨fun ⟨W⟩ ↦ W.mappedPartialCHPIn, PartialAgeIn.MappedPartialCHPIn.nonempty_hpWitnessIn⟩

end FirstOrder.Language
