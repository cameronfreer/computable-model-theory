/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PartialTheorem28

/-!
# The computable joint embedding property for Definition 2.1 families

The joint-embedding companion of `MappedPartialCHPIn`. Unlike the hereditary property, this
one **keeps a total selector**: its inputs are only a pair of member indices, and every
natural is a member index. There is no carrier-membership side condition to be c.e. about, so
nothing forces partiality here — the Level-1 boundary bites on tuples, not on indices.

The output `PartialJointEmbeddingData` is **proof-free code data** — an apex index and the two
image tuples — so it is `Primcodable` independently of any family and can be the value of a
computable selector. All semantic content sits in the soundness clause, which supplies the two
embeddings and says the image tuples record where each member's recorded generators go.

The witness oracle `E` and the presentation oracle `O` are independent, as everywhere in this
layer; `PartialCJEPIn.mono` lifts along `E ⊆ E'`.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-- Proof-free joint-embedding output: an apex index and the images of the two members'
recorded generator tuples. -/
structure PartialJointEmbeddingData where
  /-- The index of the common member both sides embed into. -/
  apexIdx : ℕ
  /-- The image of the left member's recorded generators. -/
  leftImage : Tuple ℕ
  /-- The image of the right member's recorded generators. -/
  rightImage : Tuple ℕ

/-- The code-level packaging of partial joint embedding data. -/
private def pjeEquiv : PartialJointEmbeddingData ≃ ℕ × List ℕ × List ℕ where
  toFun J := (J.apexIdx, J.leftImage, J.rightImage)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable PartialJointEmbeddingData :=
  Primcodable.ofEquiv _ pjeEquiv

theorem PartialJointEmbeddingData.primrec_apexIdx :
    Primrec PartialJointEmbeddingData.apexIdx :=
  (Primrec.fst.comp (Primrec.of_equiv (e := pjeEquiv))).of_eq fun _ ↦ rfl

theorem PartialJointEmbeddingData.primrec_leftImage :
    Primrec PartialJointEmbeddingData.leftImage :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := pjeEquiv)))).of_eq fun _ ↦ rfl

theorem PartialJointEmbeddingData.primrec_rightImage :
    Primrec PartialJointEmbeddingData.rightImage :=
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e := pjeEquiv)))).of_eq fun _ ↦ rfl

/-- The named triple → data factory, mirroring `PotentialEmbeddingData.ofTriple`. -/
def PartialJointEmbeddingData.ofTriple (p : ℕ × Tuple ℕ × Tuple ℕ) :
    PartialJointEmbeddingData :=
  pjeEquiv.symm p

@[simp]
theorem PartialJointEmbeddingData.ofTriple_apexIdx (p : ℕ × Tuple ℕ × Tuple ℕ) :
    (PartialJointEmbeddingData.ofTriple p).apexIdx = p.1 :=
  rfl

@[simp]
theorem PartialJointEmbeddingData.ofTriple_leftImage (p : ℕ × Tuple ℕ × Tuple ℕ) :
    (PartialJointEmbeddingData.ofTriple p).leftImage = p.2.1 :=
  rfl

@[simp]
theorem PartialJointEmbeddingData.ofTriple_rightImage (p : ℕ × Tuple ℕ × Tuple ℕ) :
    (PartialJointEmbeddingData.ofTriple p).rightImage = p.2.2 :=
  rfl

theorem PartialJointEmbeddingData.primrec_ofTriple :
    Primrec PartialJointEmbeddingData.ofTriple :=
  Primrec.of_equiv_symm

namespace PartialAgeIn

/-- The **computable joint embedding property**: a selector, *total* and computable in the
witness oracle `E`, carrying a pair of member indices to an apex index together with the
images there of both members' recorded generator tuples, each image realized by an actual
embedding of the member's carrier into the apex's. -/
def PartialCJEPIn (E : Set (ℕ →. ℕ)) (B : PartialAgeIn O L) : Prop :=
  ∃ sel : ℕ → ℕ → PartialJointEmbeddingData,
    ComputableIn E (fun p : ℕ × ℕ ↦ sel p.1 p.2) ∧
      ∀ i j : ℕ,
        (∃ hleft : (B.gens i).length = (sel i j).leftImage.length,
          ∃ Fi : (B.memberAt i).domain ↪[L] (B.memberAt (sel i j).apexIdx).domain,
            ∀ k : Fin (B.gens i).length,
              ((Fi ⟨(B.gens i).get k, B.gens_mem_domainAt k⟩ :
                (B.memberAt (sel i j).apexIdx).domain) : ℕ) =
                (sel i j).leftImage.get (Fin.cast hleft k)) ∧
        (∃ hright : (B.gens j).length = (sel i j).rightImage.length,
          ∃ Fj : (B.memberAt j).domain ↪[L] (B.memberAt (sel i j).apexIdx).domain,
            ∀ k : Fin (B.gens j).length,
              ((Fj ⟨(B.gens j).get k, B.gens_mem_domainAt k⟩ :
                (B.memberAt (sel i j).apexIdx).domain) : ℕ) =
                (sel i j).rightImage.get (Fin.cast hright k))

/-- The base-oracle case: the witness oracle is the presentation oracle. -/
abbrev PartialCJEP (B : PartialAgeIn O L) : Prop :=
  PartialCJEPIn O B

/-- A stronger witness oracle still witnesses: only the selector's effectivity mentions the
oracle, and the soundness clause is semantic. -/
theorem PartialCJEPIn.mono {E E' : Set (ℕ →. ℕ)} {B : PartialAgeIn O L}
    (h : PartialCJEPIn E B) (hEE' : E ⊆ E') : PartialCJEPIn E' B := by
  obtain ⟨sel, hsel, hspec⟩ := h
  exact ⟨sel, RecursiveIn.mono hEE' hsel, hspec⟩

/-- Both members embed into the apex — the joint-embedding content, with the coordinate
bookkeeping discarded. -/
theorem PartialCJEPIn.exists_apex {B : PartialAgeIn O L} (h : PartialCJEPIn E B) (i j : ℕ) :
    ∃ a : ℕ,
      Nonempty ((B.memberAt i).domain ↪[L] (B.memberAt a).domain) ∧
        Nonempty ((B.memberAt j).domain ↪[L] (B.memberAt a).domain) := by
  obtain ⟨sel, -, hspec⟩ := h
  obtain ⟨⟨-, Fi, -⟩, ⟨-, Fj, -⟩⟩ := hspec i j
  exact ⟨(sel i j).apexIdx, ⟨Fi⟩, ⟨Fj⟩⟩

end PartialAgeIn

end FirstOrder.Language
