/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.RepresentationIso
import ComputableModelTheory.ModelTheory.Computable.GraphExample
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for computable isomorphism of representations

One fixture: the **constant empty family** over the graph language, every member of which has an
empty carrier. The graph language has no function symbols, so `Term (Fin 0)` is uninhabited and
the generation law holds with an empty carrier — over a language with constants no such family
could exist.

It tests two independent things at once.

*Reflexivity is genuinely nowhere defined* on empty members. A total identity would satisfy the
type but violate the halting law, and this row is what distinguishes them.

*Arbitrary computable index maps still yield covers*, because all indexed members are
definitionally identical. Composition is therefore checked with two **different** affine index
maps, chosen so the correct reverse-order backward composite is numerically different from the
wrong order — not merely symbolically different.

The two identity mechanisms are kept apart on purpose: the production `refl` is used only where
the index map really is the identity, and a small audit-local `emptyCover` supplies nonidentity
index maps, so no row pretends `refl` supports them.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

section

variable {O : Set (ℕ →. ℕ)}

attribute [local instance] pathGraphStructure

/-- The constant empty family over the graph language: no member enumerates anything, and every
member's recorded generator tuple is empty. -/
noncomputable def emptyGraphAge : PartialAgeIn O Language.graph where
  structureAt _ := pathGraphStructure
  enum? _ _ := Option.none
  enum?_computableIn := ComputableIn.const _
  gens _ := []
  gens_computableIn := ComputableIn.const _
  funEval _ _ := Part.none
  funEval_recursiveIn := RecursiveIn.none
  funEval_correct := fun _ d _ ↦ isEmptyElim d
  relEval _ _ := Part.none
  relEval_recursiveIn := RecursiveIn.none
  relEval_correct := fun _ d h ↦ by
    match d with
    | ⟨2, _, _⟩ =>
      obtain ⟨m, hm⟩ := h 0
      exact (Option.some_ne_none _ hm.symm).elim
    | ⟨0, r, _⟩ => exact isEmptyElim r
    | ⟨1, r, _⟩ => exact isEmptyElim r
    | ⟨n + 3, r, _⟩ => exact isEmptyElim r
  generates := fun i x ↦ by
    constructor
    · rintro ⟨m, hm⟩
      exact (Option.some_ne_none _ hm.symm).elim
    · rintro ⟨T, -⟩
      induction T with
      | var k => exact k.elim0
      | func f _ _ => exact isEmptyElim f

/-- Every member of the empty family has an empty carrier. -/
theorem not_mem_emptyGraphAge_domainAt (i x : ℕ) :
    x ∉ (emptyGraphAge (O := O)).domainAt i := by
  rintro ⟨m, hm⟩
  exact (Option.some_ne_none _ hm.symm).elim

/-! ### Gate 1: reflexivity is nowhere defined on empty members -/

/-- **Reflexivity halts nowhere** on the empty family. A total identity map would typecheck but
break the halting law; this is the row that tells them apart. -/
theorem test_refl_nowhere_defined (hOE : O ⊆ O) (i x : ℕ) :
    ¬ (((RepresentationIsoIn.refl (emptyGraphAge (O := O)) hOE).forward.isoAt i).toFun x).Dom :=
  fun h ↦ not_mem_emptyGraphAge_domainAt (O := O) i x
    ((((RepresentationIsoIn.refl (emptyGraphAge (O := O)) hOE).forward.isoAt
      i).toFun_dom x).1 h)

/-- And reflexivity's index map really is the identity. -/
theorem test_refl_indexMap (hOE : O ⊆ O) (i : ℕ) :
    (RepresentationIsoIn.refl (emptyGraphAge (O := O)) hOE).forward.indexMap i = i := rfl

/-! ### An audit-local cover with an arbitrary index map

All members of the empty family are definitionally identical, so *any* computable index map
gives a cover. The maps are nowhere defined, which is exactly right on empty carriers. -/

/-- A cover of the empty family by itself along an arbitrary computable index map. -/
noncomputable def emptyCover (σ : ℕ → ℕ) (hσ : ComputableIn O σ) :
    RepresentationCoverIn O (emptyGraphAge (O := O)) (emptyGraphAge (O := O)) where
  indexMap := σ
  indexMap_computableIn := hσ
  isoAt j :=
    { toFun _ := Part.none
      invFun _ := Part.none
      toFun_recursiveIn := RecursiveIn.none
      invFun_recursiveIn := RecursiveIn.none
      toFun_dom := fun x ↦
        ⟨fun h ↦ h.elim, fun h ↦ (not_mem_emptyGraphAge_domainAt (O := O) j x h).elim⟩
      invFun_dom := fun y ↦
        ⟨fun h ↦ h.elim, fun h ↦ (not_mem_emptyGraphAge_domainAt (O := O) (σ j) y h).elim⟩
      toFun_mem := fun h ↦ h.fst.elim
      invFun_toFun := fun h ↦ h.fst.elim
      toFun_invFun := fun h ↦ h.fst.elim
      toFun_funMap := fun _ f _ _ _ ↦ isEmptyElim f
      toFun_relMap := fun n R _ _ hw ↦ by
        match n, R with
        | 2, _ => exact (hw 0).fst.elim
        | 0, R => exact isEmptyElim R
        | 1, R => exact isEmptyElim R
        | m + 3, R => exact isEmptyElim R }
  toFun_uniform := RecursiveIn.none
  invFun_uniform := RecursiveIn.none

/-! ### Gate 2: composition order

The two affine maps are chosen so that the correct reverse-order backward composite differs
**numerically** from the wrong order. Backward composition is `r.backward ∘ s.backward`, so at
`0` the correct answer is `3 * (2 * 0) + 1 = 1`, whereas composing in the forward order would
give `2 * (3 * 0 + 1) = 2`. A symbolic-only difference would not catch an accidental rewrite. -/

/-- The bidirectional isomorphism carrying index map `σ` forward and `τ` backward. -/
noncomputable def emptyIso (σ τ : ℕ → ℕ) (hσ : ComputableIn O σ) (hτ : ComputableIn O τ) :
    RepresentationIsoIn O (emptyGraphAge (O := O)) (emptyGraphAge (O := O)) where
  forward := emptyCover σ hσ
  backward := emptyCover τ hτ

/-- **Forward covers compose in order.** -/
theorem test_trans_forward_order :
    ((emptyIso (O := O) (fun n ↦ 2 * n) (fun n ↦ 3 * n + 1)
        (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).to_comp.computableIn
        ((Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) Primrec.id)
          (Primrec.const 1)).to_comp.computableIn)).trans
      (emptyIso (fun n ↦ 3 * n + 1) (fun n ↦ 2 * n)
        ((Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) Primrec.id)
          (Primrec.const 1)).to_comp.computableIn)
        (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).to_comp.computableIn)).forward.indexMap
      1 = 7 := rfl

/-- **Backward covers compose in REVERSE order** — the wrong order would give `2`, not `1`. -/
theorem test_trans_backward_order :
    ((emptyIso (O := O) (fun n ↦ 2 * n) (fun n ↦ 3 * n + 1)
        (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).to_comp.computableIn
        ((Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) Primrec.id)
          (Primrec.const 1)).to_comp.computableIn)).trans
      (emptyIso (fun n ↦ 3 * n + 1) (fun n ↦ 2 * n)
        ((Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) Primrec.id)
          (Primrec.const 1)).to_comp.computableIn)
        (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).to_comp.computableIn)).backward.indexMap
      0 = 1 := rfl

/-! ### Gate 3: symmetry, and the semantic consequence -/

/-- **Symmetry swaps the covers**: the new forward index map is the old backward one. -/
theorem test_symm_forward_eq_backward (σ τ : ℕ → ℕ) (hσ : ComputableIn O σ)
    (hτ : ComputableIn O τ) (i : ℕ) :
    (emptyIso (O := O) σ τ hσ hτ).symm.forward.indexMap i =
      (emptyIso (O := O) σ τ hσ hτ).backward.indexMap i := rfl

/-- **The semantic consequence**, with no oracle hypothesis. -/
theorem test_sameClass (σ τ : ℕ → ℕ) (hσ : ComputableIn O σ) (hτ : ComputableIn O τ) :
    (emptyGraphAge (O := O)).SameClass (emptyGraphAge (O := O)) :=
  (emptyIso σ τ hσ hτ).sameClass

end

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.test_refl_nowhere_defined
#assert_standard_axioms FirstOrder.Language.test_refl_indexMap
#assert_standard_axioms FirstOrder.Language.test_trans_forward_order
#assert_standard_axioms FirstOrder.Language.test_trans_backward_order
#assert_standard_axioms FirstOrder.Language.test_symm_forward_eq_backward
#assert_standard_axioms FirstOrder.Language.test_sameClass
