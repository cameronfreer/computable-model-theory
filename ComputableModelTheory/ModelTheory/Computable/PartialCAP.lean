/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PartialMemberEmbedding

/-!
# The computable amalgamation property for Definition 2.1 families

The general-setting counterpart of `CAPWitnessIn`, and the hypothesis CHMM's Fraïssé-limit
theorem turns on. Unlike joint embedding, this selector is **partial**: its input is span
*data* carrying range tuples, and whether those tuples land in the indicated members is only
c.e., so nothing here can be total.

The contract splits into three obligations that must not be conflated:

* **`halts`** — a *carrier-valid* input span forces the selector to converge. This is the only
  place carrier validity appears. It is deliberately weak: it says nothing about tuple lengths,
  atomic equivalence, or whether the legs are embeddings at all.
* **`unconditional`** — *any* returned diagram is index-shaped for the input span, has an
  actual left map, and has a `PartialWellFormed` right map. The single premise is
  `D ∈ sel S`. Carrier validity of the input is **not** a premise here: it governs required
  halting, not the meaning of returned outputs. Operationally this unconditional left
  embedding is what lets a stage construction keep extending through scheduled candidate maps
  that turn out invalid.
* **`sound`** — on an *actual* input span the returned diagram additionally has an actual right
  map and a commuting square.

No map-validity condition enters the selector's domain, and no exact domain is claimed: the
selector may well converge on spans that are not carrier-valid.

`PartialWellFormed` carries both the length equation and codomain membership — in the partial
setting length alone is not well-formedness, since a range tuple can point outside its member.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

namespace PartialAgeIn

/-- Full partial amalgamation: the diagram is index-shaped for the span, both output maps are
realized, and the square commutes. The analogue of
`AmalgamationDiagramData.IsAmalgamationOf`, with coded composite equality replaced by semantic
commutativity of realizers. -/
def PartialAmalgamation (B : PartialAgeIn O L) (S : PotentialSpanData)
    (D : AmalgamationDiagramData) : Prop :=
  D.WellShapedFor S ∧ B.PartialIsEmbedding D.leftToApex ∧
    B.PartialIsEmbedding D.rightToApex ∧ B.PartialCommutes S D

/-- The **computable amalgamation property**, relativized to a witness oracle. -/
def PartialCAPIn (E : Set (ℕ →. ℕ)) (B : PartialAgeIn O L) : Prop :=
  ∃ sel : PotentialSpanData →. AmalgamationDiagramData,
    RecursiveIn E sel ∧
      (∀ S : PotentialSpanData, B.CarrierValidSpan S → (sel S).Dom) ∧
      (∀ (S : PotentialSpanData) (D : AmalgamationDiagramData), D ∈ sel S →
        D.WellShapedFor S ∧ B.PartialIsEmbedding D.leftToApex ∧
          B.PartialWellFormed D.rightToApex) ∧
      (∀ (S : PotentialSpanData) (D : AmalgamationDiagramData), D ∈ sel S →
        B.PartialSpanActual S →
        B.PartialIsEmbedding D.rightToApex ∧ B.PartialCommutes S D)

/-- The base-oracle case: the witness oracle is the presentation oracle. -/
abbrev PartialCAP (B : PartialAgeIn O L) : Prop :=
  PartialCAPIn O B

/-- A stronger witness oracle still witnesses: only the selector's effectivity mentions the
oracle; halting, the unconditional clauses and soundness are all semantic. -/
theorem PartialCAPIn.mono {E E' : Set (ℕ →. ℕ)} {B : PartialAgeIn O L}
    (h : PartialCAPIn E B) (hEE' : E ⊆ E') : PartialCAPIn E' B := by
  obtain ⟨sel, hsel, hhalt, huncond, hsound⟩ := h
  exact ⟨sel, RecursiveIn.mono hEE' hsel, hhalt, huncond, hsound⟩

variable {B : PartialAgeIn O L}

/-- **The aggregate.** The unconditional clauses and conditional soundness together give full
partial amalgamation, for any returned diagram on an actual span. -/
theorem partialAmalgamation_of_clauses {S : PotentialSpanData}
    {D : AmalgamationDiagramData}
    (huncond : D.WellShapedFor S ∧ B.PartialIsEmbedding D.leftToApex ∧
      B.PartialWellFormed D.rightToApex)
    (hsound : B.PartialIsEmbedding D.rightToApex ∧ B.PartialCommutes S D) :
    B.PartialAmalgamation S D :=
  ⟨huncond.1, huncond.2.1, hsound.1, hsound.2⟩

/-- Every actual span is amalgamated. Actualness implies carrier validity, so the selector
converges; the unconditional clauses and soundness then combine. -/
theorem PartialCAPIn.exists_partialAmalgamation (h : PartialCAPIn E B)
    {S : PotentialSpanData} (hS : B.PartialSpanActual S) :
    ∃ D : AmalgamationDiagramData, B.PartialAmalgamation S D := by
  obtain ⟨sel, -, hhalt, huncond, hsound⟩ := h
  obtain ⟨D, hD⟩ := Part.dom_iff_mem.1 (hhalt S hS.carrierValidSpan)
  exact ⟨D, partialAmalgamation_of_clauses (huncond S D hD) (hsound S D hD hS)⟩

/-- The unconditional guarantees, isolated: they hold of any returned diagram with **no**
hypothesis on the input span — in particular none of carrier validity. -/
theorem PartialCAPIn.unconditional_of_mem (h : PartialCAPIn E B) :
    ∃ sel : PotentialSpanData →. AmalgamationDiagramData,
      RecursiveIn E sel ∧
        ∀ (S : PotentialSpanData) (D : AmalgamationDiagramData), D ∈ sel S →
          D.WellShapedFor S ∧ B.PartialIsEmbedding D.leftToApex ∧
            B.PartialWellFormed D.rightToApex := by
  obtain ⟨sel, hsel, -, huncond, -⟩ := h
  exact ⟨sel, hsel, huncond⟩

end PartialAgeIn

end FirstOrder.Language
