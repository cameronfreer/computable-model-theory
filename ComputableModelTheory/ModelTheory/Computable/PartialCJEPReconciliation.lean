/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.EffectiveWitnesses
import ComputableModelTheory.ModelTheory.Computable.PartialCJEP
import ComputableModelTheory.ModelTheory.Computable.PartialWitnessBridge

/-!
# The all-ℕ CJEP adapter

```
Nonempty (JEPWitnessIn E K)  ↔  PartialCJEPIn E K.toPartialAge
```

for an **arbitrary** witness oracle `E`, in the same shape as the hereditary adapter:
transformations exported separately, the logical equivalence in the `Nonempty` form, no
`O ⊆ E` in either direction.

Both selectors are total here, so no totalization is involved — the only content is a
recoding of the output and the two realized-embedding crossings of `PartialWitnessBridge`.
The recoding is the calibration this adapter exists to check: `JointEmbeddingData` carries
two full `PotentialEmbeddingData` (each with its own domain *and* codomain index), while
`PartialJointEmbeddingData` carries one apex index and two image tuples. Going out, the
common codomain is read off `WellShapedFor`; coming back, it is supplied by construction, so
well-shapedness is `rfl`.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable {K : ComputableAgeIn O L}

/-! ### Effective JEP witness → partial-family CJEP -/

open PartialAgeIn in
/-- An all-ℕ effective JEP witness is a partial-family joint-embedding selector for the
family it embeds to, at the **same** witness oracle. -/
theorem JEPWitnessIn.partialCJEPIn (W : JEPWitnessIn E K) :
    PartialAgeIn.PartialCJEPIn E K.toPartialAge := by
  refine ⟨fun i j ↦ PartialJointEmbeddingData.ofTriple
      ((W.select (i, j)).leftInto.codIdx,
        (W.select (i, j)).leftInto.rangeTuple, (W.select (i, j)).rightInto.rangeTuple),
    ?_, fun i j ↦ ?_⟩
  · exact (PartialJointEmbeddingData.primrec_ofTriple.to_comp.computableIn).comp
      (((PotentialEmbeddingData.primrec_codIdx.comp
          JointEmbeddingData.primrec_leftInto).to_comp.computableIn.comp W.computable).pair
        (((PotentialEmbeddingData.primrec_rangeTuple.comp
            JointEmbeddingData.primrec_leftInto).to_comp.computableIn.comp W.computable).pair
          ((PotentialEmbeddingData.primrec_rangeTuple.comp
            JointEmbeddingData.primrec_rightInto).to_comp.computableIn.comp W.computable)))
  · obtain ⟨⟨hdl, hdr, hcod⟩, hL, hR⟩ := W.sound i j
    exact ⟨PotentialEmbeddingData.exists_memberEmbedding_of_isEmbedding' hL hdl rfl,
      PotentialEmbeddingData.exists_memberEmbedding_of_isEmbedding' hR hdr hcod.symm⟩

/-! ### Partial-family CJEP → effective JEP witness -/

open PartialAgeIn in
/-- A partial-family joint-embedding selector for the embedded all-ℕ family is an effective
JEP witness, at the **same** witness oracle. Well-shapedness holds by construction: the apex
index is written into both legs. -/
theorem PartialAgeIn.PartialCJEPIn.nonempty_jepWitnessIn
    (h : PartialAgeIn.PartialCJEPIn E K.toPartialAge) : Nonempty (JEPWitnessIn E K) := by
  obtain ⟨sel, hsel, hspec⟩ := h
  refine ⟨{ select := fun p ↦ JointEmbeddingData.ofPair
              (PotentialEmbeddingData.ofTriple (p.1, (sel p.1 p.2).apexIdx,
                  (sel p.1 p.2).leftImage),
                PotentialEmbeddingData.ofTriple (p.2, (sel p.1 p.2).apexIdx,
                  (sel p.1 p.2).rightImage))
            computable := ?_
            sound := fun i j ↦ ?_ }⟩
  · exact (JointEmbeddingData.primrec_ofPair.to_comp.computableIn).comp
      (((PotentialEmbeddingData.primrec_ofTriple.to_comp.computableIn).comp
          (ComputableIn.fst.pair
            (((PartialJointEmbeddingData.primrec_apexIdx.to_comp.computableIn).comp hsel).pair
              ((PartialJointEmbeddingData.primrec_leftImage.to_comp.computableIn).comp
                hsel)))).pair
        ((PotentialEmbeddingData.primrec_ofTriple.to_comp.computableIn).comp
          (ComputableIn.snd.pair
            (((PartialJointEmbeddingData.primrec_apexIdx.to_comp.computableIn).comp hsel).pair
              ((PartialJointEmbeddingData.primrec_rightImage.to_comp.computableIn).comp
                hsel)))))
  · obtain ⟨⟨hlenL, GL, hGL⟩, ⟨hlenR, GR, hGR⟩⟩ := hspec i j
    exact ⟨⟨rfl, rfl, rfl⟩,
      PotentialEmbeddingData.isEmbedding_of_memberEmbedding hlenL GL hGL,
      PotentialEmbeddingData.isEmbedding_of_memberEmbedding hlenR GR hGR⟩

/-! ### The equivalence -/

/-- **The all-ℕ CJEP reconciliation.** For an arbitrary witness oracle `E`, an effective JEP
witness for an all-ℕ computable age is exactly a partial-family joint-embedding selector for
the family it embeds to. No `O ⊆ E`. -/
theorem nonempty_jepWitnessIn_iff_partialCJEPIn (K : ComputableAgeIn O L)
    (E : Set (ℕ →. ℕ)) :
    Nonempty (JEPWitnessIn E K) ↔ PartialAgeIn.PartialCJEPIn E K.toPartialAge :=
  ⟨fun ⟨W⟩ ↦ W.partialCJEPIn, PartialAgeIn.PartialCJEPIn.nonempty_jepWitnessIn⟩

end FirstOrder.Language
