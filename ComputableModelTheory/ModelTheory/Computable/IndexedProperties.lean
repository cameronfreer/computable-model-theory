/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PotentialSpan

/-!
# Indexed hereditary, joint embedding, and amalgamation properties

The computationally useful classical properties of a computable age, stated over indices
and potential embedding data — deliberately independent of Mathlib's bundled `Hereditary` /
`JointEmbedding` / `Amalgamation` predicates. The `Indexed` prefix is kept until
equivalence with the classical definitions is proved.

`JointEmbeddingData` is pure code data — two potential embeddings intended to land in a
common indexed object — `Primcodable` independently of any age, mirroring
`PotentialSpanData` / `AmalgamationDiagramData`; it is the output coding for JEP witness
selectors. Its shape predicate (`WellShapedFor i j`) is a pure index condition;
`IsJointEmbeddingOf` adds actualness of both maps.

The three properties:

* `IndexedHP`: every tuple in every indexed object is the range of an actual map from
  some indexed object — the generated substructure is again an object of the age.
* `IndexedJEP`: every pair of indices admits actual maps into a common indexed object.
* `IndexedAP`: every actual potential span has an amalgamation diagram.

Structural non-vacuity comes for free from the identity laws: the diagonal joint
embedding at any index (`exists_isJointEmbeddingOf_diag`), and the one-sided amalgamation
of a span whose left leg is the identity (`isAmalgamationOf_id_span`), where the diagram
`⟨G, id⟩` closes the span `⟨id, G⟩` by the composition identity laws.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-- Joint embedding data: two potential embeddings intended to land in a common indexed
object. Pure code data with no proof obligations; the output coding for JEP witness
selectors. -/
structure JointEmbeddingData where
  /-- The map out of the left index. -/
  leftInto : PotentialEmbeddingData
  /-- The map out of the right index. -/
  rightInto : PotentialEmbeddingData

/-- The code-level packaging of joint embedding data. -/
private def jeEquiv : JointEmbeddingData ≃ PotentialEmbeddingData × PotentialEmbeddingData where
  toFun J := (J.leftInto, J.rightInto)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable JointEmbeddingData :=
  Primcodable.ofEquiv _ jeEquiv

theorem JointEmbeddingData.primrec_leftInto : Primrec JointEmbeddingData.leftInto :=
  (Primrec.fst.comp (Primrec.of_equiv (e := jeEquiv))).of_eq fun _ ↦ rfl

theorem JointEmbeddingData.primrec_rightInto : Primrec JointEmbeddingData.rightInto :=
  (Primrec.snd.comp (Primrec.of_equiv (e := jeEquiv))).of_eq fun _ ↦ rfl

theorem JointEmbeddingData.leftInto_computable :
    ComputableIn O JointEmbeddingData.leftInto :=
  JointEmbeddingData.primrec_leftInto.to_comp.computableIn

theorem JointEmbeddingData.rightInto_computable :
    ComputableIn O JointEmbeddingData.rightInto :=
  JointEmbeddingData.primrec_rightInto.to_comp.computableIn

/-- The named pair → data factory (`jeEquiv.symm`), the analogue of
`PotentialEmbeddingData.ofTriple`: JEP witness selectors will assemble their output codes
through it. -/
def JointEmbeddingData.ofPair (p : PotentialEmbeddingData × PotentialEmbeddingData) :
    JointEmbeddingData :=
  jeEquiv.symm p

@[simp]
theorem JointEmbeddingData.ofPair_leftInto
    (p : PotentialEmbeddingData × PotentialEmbeddingData) :
    (JointEmbeddingData.ofPair p).leftInto = p.1 :=
  rfl

@[simp]
theorem JointEmbeddingData.ofPair_rightInto
    (p : PotentialEmbeddingData × PotentialEmbeddingData) :
    (JointEmbeddingData.ofPair p).rightInto = p.2 :=
  rfl

theorem JointEmbeddingData.primrec_ofPair : Primrec JointEmbeddingData.ofPair :=
  Primrec.of_equiv_symm

theorem JointEmbeddingData.ofPair_computableIn :
    ComputableIn O JointEmbeddingData.ofPair :=
  JointEmbeddingData.primrec_ofPair.to_comp.computableIn

namespace JointEmbeddingData

/-- Well-shapedness of joint embedding data for a pair of indices: the maps start at the
given indices and share their codomain. A pure index condition, independent of any age. -/
def WellShapedFor (J : JointEmbeddingData) (i j : ℕ) : Prop :=
  J.leftInto.domIdx = i ∧ J.rightInto.domIdx = j ∧ J.leftInto.codIdx = J.rightInto.codIdx

/-- `J` jointly embeds the indices `i` and `j` over `K`: well-shaped for the pair, with
both maps actual. -/
def IsJointEmbeddingOf (J : JointEmbeddingData) (K : ComputableAgeIn O L) (i j : ℕ) :
    Prop :=
  J.WellShapedFor i j ∧ J.leftInto.IsEmbedding K ∧ J.rightInto.IsEmbedding K

variable {J : JointEmbeddingData} {K : ComputableAgeIn O L} {i j : ℕ}

theorem IsJointEmbeddingOf.wellShapedFor (h : J.IsJointEmbeddingOf K i j) :
    J.WellShapedFor i j :=
  h.1

theorem IsJointEmbeddingOf.isEmbedding_leftInto (h : J.IsJointEmbeddingOf K i j) :
    J.leftInto.IsEmbedding K :=
  h.2.1

theorem IsJointEmbeddingOf.isEmbedding_rightInto (h : J.IsJointEmbeddingOf K i j) :
    J.rightInto.IsEmbedding K :=
  h.2.2

/-- The diagonal joint embedding is free: both identity maps at an index land in it. -/
theorem exists_isJointEmbeddingOf_diag (K : ComputableAgeIn O L) (i : ℕ) :
    ∃ J : JointEmbeddingData, J.IsJointEmbeddingOf K i i :=
  ⟨⟨PotentialEmbeddingData.id K i, PotentialEmbeddingData.id K i⟩,
    ⟨rfl, rfl, rfl⟩, PotentialEmbeddingData.id_isEmbedding K i,
    PotentialEmbeddingData.id_isEmbedding K i⟩

end JointEmbeddingData

namespace ComputableAgeIn

variable (K : ComputableAgeIn O L)

/-- Indexed hereditary property: every tuple in every indexed object is the range of an
actual map from some indexed object — the substructure the tuple generates is again an
object of the age, presented with the tuple as its generator image. -/
def IndexedHP : Prop :=
  ∀ (i : ℕ) (a : Tuple ℕ), ∃ j : ℕ, (⟨j, i, a⟩ : PotentialEmbeddingData).IsEmbedding K

/-- Indexed joint embedding property: every pair of indices admits actual maps into a
common indexed object. -/
def IndexedJEP : Prop :=
  ∀ i j : ℕ, ∃ J : JointEmbeddingData, J.IsJointEmbeddingOf K i j

/-- Indexed amalgamation property: every actual potential span has an amalgamation
diagram. The span's actualness sits here, in the hypothesis — matching its deliberate
absence from `IsAmalgamationOf`. -/
def IndexedAP : Prop :=
  ∀ S : PotentialSpanData, S.IsActual K →
    ∃ D : AmalgamationDiagramData, D.IsAmalgamationOf K S

/-- One-sided amalgamation is free: a span whose left leg is the identity is closed by
the diagram carrying `G` over the apex `G.codIdx`, by the composition identity laws
(`compData G (id) = G = compData (id) G`). -/
theorem isAmalgamationOf_id_span {G : PotentialEmbeddingData} (hG : G.IsEmbedding K) :
    (⟨G, PotentialEmbeddingData.id K G.codIdx⟩ :
        AmalgamationDiagramData).IsAmalgamationOf K
      ⟨PotentialEmbeddingData.id K G.domIdx, G⟩ :=
  ⟨⟨rfl, rfl, rfl⟩, hG, PotentialEmbeddingData.id_isEmbedding K G.codIdx,
    (K.compData_id_right hG).trans (K.compData_id_left G).symm⟩

end ComputableAgeIn

end FirstOrder.Language
