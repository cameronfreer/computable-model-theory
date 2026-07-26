/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.EffectiveWitnesses
import ComputableModelTheory.ModelTheory.Computable.PartialCAPBridge

/-!
# The all-ℕ CAP adapter

```
Nonempty (CAPWitnessIn E K)  ↔  PartialCAPIn E K.toPartialAge
```

for an **arbitrary** witness oracle `E`, in the same shape as the hereditary and
joint-embedding adapters: transformations exported separately, the equivalence in the
`Nonempty` form, no `O ⊆ E`.

With the collapse lemmas of `PartialCAPBridge` in place this is mechanical. Going out, the
total selector becomes partial by `Part.some` and halting is immediate. Coming back, carrier
validity is automatic on a full carrier, so the partial selector converges on *every* raw
span and `RecursiveIn.computableIn_get` totalizes it; the membership of the selected value in
`sel S` is recorded once and reused for the unconditional clauses **and** for soundness, which
is what supplies the output shape and both output actualness witnesses needed to instantiate
`partialCommutes_iff_isAmalgamationOf` without reconstructing anything.

The partial contract's off-carrier behavior is invisible from here — every raw span is
carrier-valid on a full carrier — so this equivalence does not, and cannot, exercise it.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable {K : ComputableAgeIn O L}

/-! ### Effective CAP witness → partial-family CAP -/

open PartialAgeIn in
/-- An all-ℕ effective CAP witness is a partial-family amalgamation selector for the family it
embeds to, at the **same** witness oracle. -/
theorem CAPWitnessIn.partialCAPIn (W : CAPWitnessIn E K) :
    PartialAgeIn.PartialCAPIn E K.toPartialAge := by
  refine ⟨fun S ↦ Part.some (W.select S), W.computable, fun S _ ↦ trivial, ?_, ?_⟩
  · rintro S D hD
    rw [Part.mem_some_iff] at hD
    subst hD
    exact ⟨W.shape S, partialIsEmbedding_iff_isEmbedding.2 (W.leftToApex_isEmbedding S),
      partialWellFormed_iff_wellFormed.2 (W.rightToApex_wellFormed S)⟩
  · rintro S D hD hS
    rw [Part.mem_some_iff] at hD
    subst hD
    obtain ⟨hSd, ⟨hSlwf, hSlAE⟩, ⟨hSrwf, hSrAE⟩⟩ := partialSpanActual_iff_isActual.1 hS
    have hamal := W.sound S (partialSpanActual_iff_isActual.1 hS)
    obtain ⟨hlwf, hlAE⟩ := hamal.2.1
    obtain ⟨hrwf, hrAE⟩ := hamal.2.2.1
    exact ⟨partialIsEmbedding_iff_isEmbedding.2 hamal.2.2.1,
      (partialCommutes_iff_isAmalgamationOf hSd hamal.1 hSlwf hSlAE hSrwf hSrAE hlwf hlAE
        hrwf hrAE).2 hamal⟩

/-! ### Partial-family CAP → effective CAP witness -/

open PartialAgeIn in
/-- A partial-family amalgamation selector for the embedded all-ℕ family is an effective CAP
witness, at the **same** witness oracle. Carrier validity is automatic, so the selector
converges on every raw span and totalizes. -/
theorem PartialAgeIn.PartialCAPIn.nonempty_capWitnessIn
    (h : PartialAgeIn.PartialCAPIn E K.toPartialAge) : Nonempty (CAPWitnessIn E K) := by
  obtain ⟨sel, hsel, hhalt, huncond, hsound⟩ := h
  have htot : ∀ S : PotentialSpanData, (sel S).Dom :=
    fun S ↦ hhalt S (carrierValidSpan_toPartialAge K S)
  have hmem : ∀ S : PotentialSpanData, (sel S).get (htot S) ∈ sel S :=
    fun S ↦ Part.get_mem _
  refine ⟨{ select := fun S ↦ (sel S).get (htot S)
            computable := hsel.computableIn_get htot
            shape := fun S ↦ (huncond S _ (hmem S)).1
            leftToApex_isEmbedding := fun S ↦
              partialIsEmbedding_iff_isEmbedding.1 (huncond S _ (hmem S)).2.1
            rightToApex_wellFormed := fun S ↦
              partialWellFormed_iff_wellFormed.1 (huncond S _ (hmem S)).2.2
            sound := fun S hS ↦ ?_ }⟩
  obtain ⟨hshape, hleft, -⟩ := huncond S _ (hmem S)
  obtain ⟨hright, hcomm⟩ :=
    hsound S _ (hmem S) (partialSpanActual_iff_isActual.2 hS)
  obtain ⟨hSd, ⟨hSlwf, hSlAE⟩, ⟨hSrwf, hSrAE⟩⟩ := hS
  obtain ⟨hlwf, hlAE⟩ := partialIsEmbedding_iff_isEmbedding.1 hleft
  obtain ⟨hrwf, hrAE⟩ := partialIsEmbedding_iff_isEmbedding.1 hright
  exact (partialCommutes_iff_isAmalgamationOf hSd hshape hSlwf hSlAE hSrwf hSrAE hlwf hlAE
    hrwf hrAE).1 hcomm

/-! ### The equivalence -/

/-- **The all-ℕ CAP reconciliation.** For an arbitrary witness oracle `E`, an effective CAP
witness for an all-ℕ computable age is exactly a partial-family amalgamation selector for the
family it embeds to. No `O ⊆ E`: the presentation oracle enters neither direction. -/
theorem nonempty_capWitnessIn_iff_partialCAPIn (K : ComputableAgeIn O L)
    (E : Set (ℕ →. ℕ)) :
    Nonempty (CAPWitnessIn E K) ↔ PartialAgeIn.PartialCAPIn E K.toPartialAge :=
  ⟨fun ⟨W⟩ ↦ W.partialCAPIn, PartialAgeIn.PartialCAPIn.nonempty_capWitnessIn⟩

end FirstOrder.Language
