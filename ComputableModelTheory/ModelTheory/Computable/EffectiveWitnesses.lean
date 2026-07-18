/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.IndexedProperties

/-!
# Effective HP/JEP/AP witness interfaces

Total algorithms with conditional soundness for the indexed classical properties. Each
witness structure packages a total selector on code data, its computability in an oracle
set `E` (which may properly extend the age's base oracle — witness extraction will later
assume `O ⊆ E` together with an EI-decision interface), and a soundness law tying the
selected output to the corresponding indexed property:

* `HPWitnessIn E K`: from an index and a tuple, select the index of an object presenting
  the generated substructure — sound unconditionally, since every tuple of naturals is a
  tuple of the presentation.
* `JEPWitnessIn E K`: from a pair of indices, select joint embedding data — sound
  unconditionally.
* `APWitnessIn E K`: from a potential span, select an amalgamation diagram — sound only
  on actual spans. Selectors are total on arbitrary codes, so the span's actualness is a
  hypothesis of the soundness law, matching its deliberate absence from
  `IsAmalgamationOf`.
* `CAPWitnessIn E K`: the faithful computable-amalgamation interface — `APWitnessIn`'s
  contract plus the **unconditional** clauses the totalization convention demands on
  every raw span code (index shape, left-map actualness, right-map well-formedness),
  with the derived `toAPWitnessIn` sharing the selector and its computability proof
  unchanged.

Interfaces only: no witness is constructed here, and none is claimed to exist. The
existence of a witness immediately yields the corresponding indexed property
(`HPWitnessIn.indexedHP`, `JEPWitnessIn.indexedJEP`, `APWitnessIn.indexedAP`,
`CAPWitnessIn.indexedAP`).
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-- An effective HP witness: a total selector carrying an index and a tuple to the index
of an object presenting the generated substructure, computable in `E`, whose selected
potential embedding data is always actual. -/
structure HPWitnessIn (E : Set (ℕ →. ℕ)) (K : ComputableAgeIn O L) where
  /-- The selector: from a codomain index and a range tuple, the domain index. -/
  select : ℕ × Tuple ℕ → ℕ
  /-- The selector is computable in `E`. -/
  computable : ComputableIn E select
  /-- The selected data is actual: the tuple is the range of an actual map from the
  selected object. -/
  sound : ∀ (i : ℕ) (a : Tuple ℕ),
    (⟨select (i, a), i, a⟩ : PotentialEmbeddingData).IsEmbedding K

/-- An effective JEP witness: a total selector carrying a pair of indices to joint
embedding data, computable in `E`, whose output always jointly embeds the pair. -/
structure JEPWitnessIn (E : Set (ℕ →. ℕ)) (K : ComputableAgeIn O L) where
  /-- The selector: from a pair of indices, joint embedding data. -/
  select : ℕ × ℕ → JointEmbeddingData
  /-- The selector is computable in `E`. -/
  computable : ComputableIn E select
  /-- The selected data jointly embeds the pair. -/
  sound : ∀ i j : ℕ, (select (i, j)).IsJointEmbeddingOf K i j

/-- An effective AP witness: a total selector carrying a potential span to an
amalgamation diagram, computable in `E`, whose output amalgamates every *actual* span.
Totality on arbitrary codes is unconditional; soundness carries the actualness
hypothesis. -/
structure APWitnessIn (E : Set (ℕ →. ℕ)) (K : ComputableAgeIn O L) where
  /-- The selector: from span data, diagram data. -/
  select : PotentialSpanData → AmalgamationDiagramData
  /-- The selector is computable in `E`. -/
  computable : ComputableIn E select
  /-- On actual spans, the selected diagram amalgamates. -/
  sound : ∀ S : PotentialSpanData, S.IsActual K → (select S).IsAmalgamationOf K S

/-- An effective CAP witness — the faithful interface for the computable amalgamation
property, whose totalization convention demands more than `APWitnessIn`: *"even if `f`
and `g` do not extend to embeddings, we ask for `e` to extend to an embedding"*. On
**every raw span code** — whether an *invalid map* (well-shaped codes whose maps fail
to be actual, the case the convention totalizes over) or an *entirely malformed code*
(e.g. wrong tuple lengths) — the selected diagram is index-shaped for the input, its
left map is actual, and its right map is at least well-formed (a genuine map from its
generator tuple, even when not an embedding). Full actualness and coded commutativity
are conditional on exactly `S.IsActual K` — no hidden EI-decision or decidability
premise. Operationally, the unconditional left embedding is what lets a chain
construction keep extending through scheduled candidate maps that turn out invalid.

No existence or extraction theorem for such witnesses appears here; search-based
extraction belongs downstream, under its explicit search hypotheses. -/
structure CAPWitnessIn (E : Set (ℕ →. ℕ)) (K : ComputableAgeIn O L) where
  /-- The selector: from span data, diagram data. -/
  select : PotentialSpanData → AmalgamationDiagramData
  /-- The selector is computable in `E`. -/
  computable : ComputableIn E select
  /-- Unconditional: the selected diagram is index-shaped for the input span. -/
  shape : ∀ S : PotentialSpanData, (select S).WellShapedFor S
  /-- Unconditional: the selected left map is actual. -/
  leftToApex_isEmbedding : ∀ S : PotentialSpanData,
    (select S).leftToApex.IsEmbedding K
  /-- Unconditional: the selected right map is well-formed. -/
  rightToApex_wellFormed : ∀ S : PotentialSpanData,
    (select S).rightToApex.WellFormed K
  /-- On actual spans, the selected diagram amalgamates. -/
  sound : ∀ S : PotentialSpanData, S.IsActual K → (select S).IsAmalgamationOf K S

variable {E : Set (ℕ →. ℕ)} {K : ComputableAgeIn O L}

/-- The derived AP witness of a CAP witness: the selector and its computability proof
are shared **unchanged** — only the unconditional clauses are forgotten. -/
def CAPWitnessIn.toAPWitnessIn (W : CAPWitnessIn E K) : APWitnessIn E K where
  select := W.select
  computable := W.computable
  sound := W.sound

@[simp]
theorem CAPWitnessIn.toAPWitnessIn_select (W : CAPWitnessIn E K) :
    W.toAPWitnessIn.select = W.select :=
  rfl

/-- An HP witness yields the indexed hereditary property. -/
theorem HPWitnessIn.indexedHP (W : HPWitnessIn E K) : K.IndexedHP :=
  fun i a ↦ ⟨W.select (i, a), W.sound i a⟩

/-- A JEP witness yields the indexed joint embedding property. -/
theorem JEPWitnessIn.indexedJEP (W : JEPWitnessIn E K) : K.IndexedJEP :=
  fun i j ↦ ⟨W.select (i, j), W.sound i j⟩

/-- An AP witness yields the indexed amalgamation property. -/
theorem APWitnessIn.indexedAP (W : APWitnessIn E K) : K.IndexedAP :=
  fun S hS ↦ ⟨W.select S, W.sound S hS⟩

/-- A CAP witness yields the indexed amalgamation property, through its derived AP
witness. -/
theorem CAPWitnessIn.indexedAP (W : CAPWitnessIn E K) : K.IndexedAP :=
  W.toAPWitnessIn.indexedAP

end FirstOrder.Language
