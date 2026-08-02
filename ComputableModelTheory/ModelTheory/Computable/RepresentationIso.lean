/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PartialComputableIso

/-!
# Covers of one representation by another

CHMM Definition 2.3 asks for **one computable sequence in each direction**: for every member of
each representation, an index in the other together with an isomorphism, uniformly computable.
It does *not* ask that the two index maps be inverse to one another, and it does not prevent a
representation from containing different numbers of copies of an isomorphism type.

A `RepresentationCoverIn` is exactly **one** of those two directions. It claims that every member
of the source is matched, and claims nothing about which target indices are hit — a cover need
not be surjective on indices, and has no meaningful `symm`. The paper-facing notion is the
bidirectional wrapper built from two independently supplied covers.

The uniformity fields are not derivable from the per-index isomorphisms: each `isoAt i` carries
its own recursiveness proof, but a family of proofs is not a proof about the family. This is the
same trap `UniformCeIsoFamilyIn` records at the nonempty layer.

The map oracle `E` is separate from the family oracle `O`, inherited from `PartialCeIsoIn`.
Recorded here because it will matter when the wrapper's groupoid laws arrive:

* symmetry needs **no** oracle inclusion — it swaps the two stored covers;
* reflexivity needs `O ⊆ E`, since the domain-restricted identity has to recognize an `O`-c.e.
  member domain and is therefore not automatically `E`-recursive;
* transitivity needs no inclusion once both covers are already in `E`.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-- **One direction of CHMM Definition 2.3.** A computable index map together with a uniformly
computable family of isomorphisms matching each member of `A` to a member of `B`.

No claim is made about coverage of arbitrary indices of `B`. -/
structure RepresentationCoverIn (E : Set (ℕ →. ℕ)) (A B : PartialAgeIn O L) where
  /-- Where each source member is matched. -/
  indexMap : ℕ → ℕ
  indexMap_computableIn : ComputableIn E indexMap
  /-- The matching isomorphism at each index. -/
  isoAt : ∀ i, PartialCeIsoIn E (A.memberAt i) (B.memberAt (indexMap i))
  /-- Uniformity of the forward maps. Not implied by the per-index proofs in `isoAt`. -/
  toFun_uniform : RecursiveIn E fun p : ℕ × ℕ ↦ (isoAt p.1).toFun p.2
  /-- Uniformity of the backward maps. -/
  invFun_uniform : RecursiveIn E fun p : ℕ × ℕ ↦ (isoAt p.1).invFun p.2

namespace RepresentationCoverIn

variable {A B C : PartialAgeIn O L}

/-- Covers compose. There is deliberately no `symm`: a cover claims nothing about which target
indices are hit. -/
noncomputable def trans (r : RepresentationCoverIn E A B)
    (s : RepresentationCoverIn E B C) : RepresentationCoverIn E A C where
  indexMap i := s.indexMap (r.indexMap i)
  indexMap_computableIn := s.indexMap_computableIn.comp r.indexMap_computableIn
  isoAt i := (r.isoAt i).trans (s.isoAt (r.indexMap i))
  toFun_uniform := by
    have hg : RecursiveIn₂ E fun (p : ℕ × ℕ) (y : ℕ) ↦
        (s.isoAt (r.indexMap p.1)).toFun y :=
      (s.toFun_uniform.comp
        ((r.indexMap_computableIn.comp (ComputableIn.fst.comp ComputableIn.fst)).pair
          ComputableIn.snd)).to₂
    exact RecursiveIn.bind r.toFun_uniform hg
  invFun_uniform := by
    have hg : RecursiveIn₂ E fun (p : ℕ × ℕ) (y : ℕ) ↦ (r.isoAt p.1).invFun y :=
      (r.invFun_uniform.comp
        ((ComputableIn.fst.comp ComputableIn.fst).pair ComputableIn.snd)).to₂
    have hs : RecursiveIn E fun p : ℕ × ℕ ↦ (s.isoAt (r.indexMap p.1)).invFun p.2 :=
      s.invFun_uniform.comp
        ((r.indexMap_computableIn.comp ComputableIn.fst).pair ComputableIn.snd)
    exact RecursiveIn.bind hs hg

@[simp] theorem trans_indexMap (r : RepresentationCoverIn E A B)
    (s : RepresentationCoverIn E B C) (i : ℕ) :
    (r.trans s).indexMap i = s.indexMap (r.indexMap i) := rfl

end RepresentationCoverIn

/-! ### The paper-facing notion

CHMM Definition 2.3: two covers, one in each direction, **independently supplied**. No equation
relates the two index maps. That is not an omission — the paper allows the representations to
contain different numbers of copies of an isomorphism type, so requiring the index maps to be
mutually inverse would be strictly stronger than the definition. -/

/-- **Computable isomorphism of representations** (CHMM Definition 2.3): a cover in each
direction. -/
structure RepresentationIsoIn (E : Set (ℕ →. ℕ)) (A B : PartialAgeIn O L) where
  /-- Every member of `A` is matched in `B`. -/
  forward : RepresentationCoverIn E A B
  /-- Every member of `B` is matched in `A`. -/
  backward : RepresentationCoverIn E B A

namespace RepresentationIsoIn

variable {A B C : PartialAgeIn O L}

/-- Symmetry: swap the two stored covers. Needs no oracle hypothesis, and — crucially — could
not be obtained from `forward` alone, since a cover has no inverse. -/
def symm (r : RepresentationIsoIn E A B) : RepresentationIsoIn E B A where
  forward := r.backward
  backward := r.forward

@[simp] theorem symm_forward (r : RepresentationIsoIn E A B) :
    r.symm.forward = r.backward := rfl

@[simp] theorem symm_backward (r : RepresentationIsoIn E A B) :
    r.symm.backward = r.forward := rfl

@[simp] theorem symm_symm (r : RepresentationIsoIn E A B) : r.symm.symm = r := rfl

/-- Composition: forward covers compose in order, backward covers in the **reverse** order. -/
noncomputable def trans (r : RepresentationIsoIn E A B)
    (s : RepresentationIsoIn E B C) : RepresentationIsoIn E A C where
  forward := r.forward.trans s.forward
  backward := s.backward.trans r.backward

@[simp] theorem trans_forward_indexMap (r : RepresentationIsoIn E A B)
    (s : RepresentationIsoIn E B C) (i : ℕ) :
    (r.trans s).forward.indexMap i = s.forward.indexMap (r.forward.indexMap i) := rfl

@[simp] theorem trans_backward_indexMap (r : RepresentationIsoIn E A B)
    (s : RepresentationIsoIn E B C) (i : ℕ) :
    (r.trans s).backward.indexMap i = r.backward.indexMap (s.backward.indexMap i) := rfl

end RepresentationIsoIn

end FirstOrder.Language
