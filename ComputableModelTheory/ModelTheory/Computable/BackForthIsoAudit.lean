/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.BackForthIso
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: Proposition 3.2

**The nullary cases are the ones the stage bounds exist for.** With no arguments `argsStage` is `0`,
so a nullary *relation* is decided at stage `0` — `test_nullary_relation` records that, and it is the
case where the argument bound carries the whole statement. A nullary *function* is the opposite:
`test_nullary_function` shows its argument bound is also `0` while its stage is
`funMap f v + 1`, which is where the output bound does all the work. Dropping the output bound from
`funStage` would leave exactly this case unprovable, and no other row would notice.

**Relations are reflected, not only preserved.** `test_relation_reflects` gives the direction an
embedding-only argument would not: from a relation holding of the images, it holds of the arguments.
`map_rel'` is an `iff`, and this row is what would fail if it were ever weakened to an implication.

**The package pins its two covers and its two selectors.** `test_package_maps` reads the fields back
as the maps built from `r.forward` and `r.backward`, in that order, with the **target**'s homogeneity
driving the forth half and the **source**'s the back half. Swapping either pair typechecks, since
both have the same shape after the structures are swapped, so the equations are the gate.

**No `O ⊆ E`.** Every row here takes structures presented at `O` and data at an arbitrary `E`, with
no hypothesis relating them.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

section Iso

variable {E : Set (ℕ →. ℕ)} {S T : ComputableStructureIn O L}
  (r : RepresentationCoverIn E S.canonicalAge T.canonicalAge)
  (rb : RepresentationCoverIn E T.canonicalAge S.canonicalAge)
  (H : ComputablyHomogeneousIn E T) (Hs : ComputablyHomogeneousIn E S)

/-! ### The stage bounds -/

/-- **A nullary function.** No arguments, so the argument bound is `0` — and the stage is entirely
the output bound. This is the case that would break if `funStage` were `argsStage`. -/
theorem test_nullary_function (fs : L.Functions 0) (v : Fin 0 → ℕ) :
    argsStage v = 0 ∧
      funStage S fs v = @Structure.funMap L ℕ S.inst 0 fs v + 1 ∧
        BackForthState.toFun r rb H Hs (@Structure.funMap L ℕ S.inst 0 fs v)
          = @Structure.funMap L ℕ T.inst 0 fs fun k ↦ BackForthState.toFun r rb H Hs (v k) := by
  refine ⟨argsStage_of_isEmpty v rfl, ?_, BackForthState.toFun_funMap r rb H Hs fs v⟩
  rw [funStage, argsStage_of_isEmpty v rfl]
  omega

/-- **A nullary relation is decided at stage `0`.** Nothing has to be matched first. -/
theorem test_nullary_relation (R : L.Relations 0) (v : Fin 0 → ℕ) :
    argsStage v = 0 ∧
      (@Structure.RelMap L ℕ T.inst 0 R (fun k ↦ BackForthState.toFun r rb H Hs (v k))
        ↔ @Structure.RelMap L ℕ S.inst 0 R v) :=
  ⟨argsStage_of_isEmpty v rfl, BackForthState.toFun_relMap r rb H Hs R v⟩

/-- The general bounds, read back: every argument is matched by `funStage`, and so is the value. -/
theorem test_fun_stage_bounds {n : ℕ} (fs : L.Functions n) (v : Fin n → ℕ) :
    (∀ k, v k + 1 ≤ funStage S fs v) ∧
      @Structure.funMap L ℕ S.inst n fs v + 1 ≤ funStage S fs v ∧
        ∀ k, v k + 1 ≤ argsStage v :=
  ⟨le_funStage_of_arg S fs v, funMap_lt_funStage S fs v, le_argsStage v⟩

/-! ### The structure laws -/

/-- The function law, at an arbitrary arity. -/
theorem test_toFun_funMap {n : ℕ} (fs : L.Functions n) (v : Fin n → ℕ) :
    BackForthState.toFun r rb H Hs (@Structure.funMap L ℕ S.inst n fs v)
      = @Structure.funMap L ℕ T.inst n fs fun k ↦ BackForthState.toFun r rb H Hs (v k) :=
  BackForthState.toFun_funMap r rb H Hs fs v

/-- **Relations are reflected.** From the images satisfying the relation, the arguments do — the
direction that distinguishes an isomorphism from an embedding. -/
theorem test_relation_reflects {n : ℕ} (R : L.Relations n) (v : Fin n → ℕ)
    (h : @Structure.RelMap L ℕ T.inst n R fun k ↦ BackForthState.toFun r rb H Hs (v k)) :
    @Structure.RelMap L ℕ S.inst n R v :=
  (BackForthState.toFun_relMap r rb H Hs R v).mp h

/-- And preserved. -/
theorem test_relation_preserves {n : ℕ} (R : L.Relations n) (v : Fin n → ℕ)
    (h : @Structure.RelMap L ℕ S.inst n R v) :
    @Structure.RelMap L ℕ T.inst n R fun k ↦ BackForthState.toFun r rb H Hs (v k) :=
  (BackForthState.toFun_relMap r rb H Hs R v).mpr h

end Iso

/-! ### The package -/

section Package

variable {E : Set (ℕ →. ℕ)} {S T : ComputableStructureIn O L}

/-- **The package's maps, with both covers and both selectors pinned.** The forward map is built
from `r.forward` as the forth cover and `r.backward` as the back cover, with the **target**'s
homogeneity in the forth position and the **source**'s in the back position. -/
theorem test_package_maps (r : RepresentationIsoIn E S.canonicalAge T.canonicalAge)
    (Hs : ComputablyHomogeneousIn E S) (Ht : ComputablyHomogeneousIn E T) :
    (backForthIso r Hs Ht).toFun = BackForthState.toFun r.forward r.backward Ht Hs ∧
      (backForthIso r Hs Ht).invFun = BackForthState.invFun r.forward r.backward Ht Hs :=
  ⟨rfl, rfl⟩

/-- **Proposition 3.2, with `O` and `E` unrelated.** The structures are presented at `O`; the
isomorphism of representations and both homogeneity selectors live at an arbitrary `E`; no inclusion
between them appears. -/
theorem test_proposition_3_2 (r : RepresentationIsoIn E S.canonicalAge T.canonicalAge)
    (Hs : ComputablyHomogeneousIn E S) (Ht : ComputablyHomogeneousIn E T) :
    Nonempty (ComputableStructureIsoIn E S T) :=
  ⟨backForthIso r Hs Ht⟩

/-- All eight fields of the package, read back at once. -/
theorem test_package_laws (r : RepresentationIsoIn E S.canonicalAge T.canonicalAge)
    (Hs : ComputablyHomogeneousIn E S) (Ht : ComputablyHomogeneousIn E T) :
    ComputableIn E (backForthIso r Hs Ht).toFun ∧
      ComputableIn E (backForthIso r Hs Ht).invFun ∧
        (∀ x, (backForthIso r Hs Ht).invFun ((backForthIso r Hs Ht).toFun x) = x) ∧
          (∀ y, (backForthIso r Hs Ht).toFun ((backForthIso r Hs Ht).invFun y) = y) ∧
            (∀ (n : ℕ) (f : L.Functions n) (v : Fin n → ℕ),
              (backForthIso r Hs Ht).toFun (@Structure.funMap L ℕ S.inst n f v)
                = @Structure.funMap L ℕ T.inst n f fun k ↦ (backForthIso r Hs Ht).toFun (v k)) ∧
              ∀ (n : ℕ) (R : L.Relations n) (v : Fin n → ℕ),
                @Structure.RelMap L ℕ T.inst n R (fun k ↦ (backForthIso r Hs Ht).toFun (v k))
                  ↔ @Structure.RelMap L ℕ S.inst n R v :=
  ⟨(backForthIso r Hs Ht).toFun_computableIn, (backForthIso r Hs Ht).invFun_computableIn,
    (backForthIso r Hs Ht).left_inv, (backForthIso r Hs Ht).right_inv,
    (backForthIso r Hs Ht).toFun_funMap, (backForthIso r Hs Ht).toFun_relMap⟩

/-- The forward map is a bijection, so the isomorphism is one in the ordinary sense too. -/
theorem test_package_bijective (r : RepresentationIsoIn E S.canonicalAge T.canonicalAge)
    (Hs : ComputablyHomogeneousIn E S) (Ht : ComputablyHomogeneousIn E T) :
    Function.Bijective (backForthIso r Hs Ht).toFun :=
  (backForthIso r Hs Ht).toFun_bijective

end Package

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.test_nullary_function
#assert_standard_axioms FirstOrder.Language.test_nullary_relation
#assert_standard_axioms FirstOrder.Language.test_fun_stage_bounds
#assert_standard_axioms FirstOrder.Language.test_toFun_funMap
#assert_standard_axioms FirstOrder.Language.test_relation_reflects
#assert_standard_axioms FirstOrder.Language.test_relation_preserves
#assert_standard_axioms FirstOrder.Language.test_package_maps
#assert_standard_axioms FirstOrder.Language.test_proposition_3_2
#assert_standard_axioms FirstOrder.Language.test_package_laws
#assert_standard_axioms FirstOrder.Language.test_package_bijective
