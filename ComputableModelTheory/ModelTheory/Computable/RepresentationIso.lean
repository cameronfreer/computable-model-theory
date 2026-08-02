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

end FirstOrder.Language
