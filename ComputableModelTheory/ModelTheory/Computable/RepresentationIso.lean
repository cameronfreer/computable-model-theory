/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PartialComputableIso
import ComputableModelTheory.ModelTheory.Computable.PartialAgeSteps

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
The oracle facts for the wrapper's groupoid operations:

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

/-! ### The uniform partial identity

One program, used both per-index and as the uniformity witness, so the two are literally the
same rather than merely extensionally equal. It halts exactly on the member's carrier — a total
identity would overclaim the domain — and the oracle lift happens once, at the boundary. -/

/-- The domain-restricted identity of a family: search for an enumeration witness, then return
the queried value. -/
noncomputable def PartialAgeIn.idFun (A : PartialAgeIn O L) (p : ℕ × ℕ) : Part ℕ :=
  (A.firstStepFor p.1 p.2).map fun _ ↦ p.2

theorem PartialAgeIn.idFun_recursiveIn (A : PartialAgeIn O L) :
    RecursiveIn O A.idFun :=
  RecursiveIn.map A.firstStepFor_recursiveIn
    (ComputableIn.snd.comp ComputableIn.fst).to₂

theorem PartialAgeIn.idFun_dom (A : PartialAgeIn O L) (i x : ℕ) :
    (A.idFun (i, x)).Dom ↔ x ∈ A.domainAt i :=
  A.firstStepFor_dom_iff

theorem PartialAgeIn.mem_idFun (A : PartialAgeIn O L) {i x y : ℕ} :
    y ∈ A.idFun (i, x) ↔ y = x ∧ x ∈ A.domainAt i := by
  rw [PartialAgeIn.idFun, Part.mem_map_iff]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨rfl, A.firstStepFor_dom_iff.1 (Part.dom_iff_mem.2 ⟨m, hm⟩)⟩
  · rintro ⟨rfl, hx⟩
    obtain ⟨m, hm⟩ := Part.dom_iff_mem.1 (A.firstStepFor_dom_iff.2 hx)
    exact ⟨m, hm, rfl⟩

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

/-- **Reflexivity.** Needs `O ⊆ E`: the identity has to recognize an `O`-c.e. member domain, so
it is not automatically `E`-recursive. Every `isoAt i` is the one uniform program applied at `i`,
so the per-index maps and the uniformity fields are literally the same program. -/
noncomputable def refl (A : PartialAgeIn O L) (hOE : O ⊆ E) :
    RepresentationCoverIn E A A where
  indexMap i := i
  indexMap_computableIn := ComputableIn.id
  isoAt i :=
    { toFun := fun x ↦ A.idFun (i, x)
      invFun := fun x ↦ A.idFun (i, x)
      toFun_recursiveIn :=
        (RecursiveIn.mono hOE A.idFun_recursiveIn).comp
          ((ComputableIn.const i).pair ComputableIn.id)
      invFun_recursiveIn :=
        (RecursiveIn.mono hOE A.idFun_recursiveIn).comp
          ((ComputableIn.const i).pair ComputableIn.id)
      toFun_dom := fun x ↦ A.idFun_dom i x
      invFun_dom := fun x ↦ A.idFun_dom i x
      toFun_mem := fun h ↦ by
        obtain ⟨rfl, hx⟩ := A.mem_idFun.1 h
        exact hx
      invFun_toFun := fun h ↦ by
        obtain ⟨rfl, hx⟩ := A.mem_idFun.1 h
        exact A.mem_idFun.2 ⟨rfl, hx⟩
      toFun_invFun := fun h ↦ by
        obtain ⟨rfl, hx⟩ := A.mem_idFun.1 h
        exact A.mem_idFun.2 ⟨rfl, hx⟩
      toFun_funMap := fun n f v w hw ↦ by
        have hvw : ∀ k, w k = v k := fun k ↦ (A.mem_idFun.1 (hw k)).1
        have hv : ∀ k, v k ∈ A.domainAt i := fun k ↦ (A.mem_idFun.1 (hw k)).2
        rw [show w = v from funext hvw]
        exact A.mem_idFun.2 ⟨rfl, A.domainAt_closed f hv⟩
      toFun_relMap := fun n R v w hw ↦ by
        have hvw : ∀ k, w k = v k := fun k ↦ (A.mem_idFun.1 (hw k)).1
        rw [show w = v from funext hvw] }
  toFun_uniform := RecursiveIn.mono hOE A.idFun_recursiveIn
  invFun_uniform := RecursiveIn.mono hOE A.idFun_recursiveIn

@[simp] theorem refl_indexMap (A : PartialAgeIn O L) (hOE : O ⊆ E) (i : ℕ) :
    (RepresentationCoverIn.refl A hOE (E := E)).indexMap i = i := rfl

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

/-- **Reflexivity**, reusing one cover for both directions. -/
noncomputable def refl (A : PartialAgeIn O L) (hOE : O ⊆ E) : RepresentationIsoIn E A A where
  forward := RepresentationCoverIn.refl A hOE
  backward := RepresentationCoverIn.refl A hOE

/-- **The semantic consequence.** A computable isomorphism of representations presents the same
class of structures. No oracle hypothesis: each direction reads off the stored index map and
wraps the corresponding member isomorphism's induced first-order equivalence. -/
theorem sameClass (r : RepresentationIsoIn E A B) : A.SameClass B :=
  ⟨fun i ↦ ⟨r.forward.indexMap i, ⟨(r.forward.isoAt i).toEquiv⟩⟩,
    fun j ↦ ⟨r.backward.indexMap j, ⟨(r.backward.isoAt j).toEquiv⟩⟩⟩

end RepresentationIsoIn

end FirstOrder.Language
