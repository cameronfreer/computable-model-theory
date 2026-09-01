/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.BackForthMaps

/-!
# CHMM Proposition 3.2 — the computable isomorphism

The limit map is an isomorphism. What remains after the inverse laws is that it preserves the
structure, and that is a matter of finding **one stage at which everything in sight is already
matched**, then reading the laws off that stage's realizer.

## Which stage

`argsStage v` is the least stage by which every argument has been matched — a `Finset.sup` of
`v k + 1`, so `Fin 0` gives `0` and the empty case is handled without a special clause.

For a **function** application that is not enough: the value `funMap f v` must itself be recorded, so
`funStage f v` maxes the argument bound with `funMap f v + 1`. That extra bound is exactly what makes
the nullary case work — a constant has no arguments, so `argsStage` is `0`, yet its value still has
to be present. For a **relation** the arguments suffice; nothing else appears in the statement.

## How the laws come out

At a matched stage the realizer is an `L`-embedding between the two generated members, and the
members' structures are the ambient ones on the underlying values by construction of `subtypeStr`.
So `map_fun'` and `map_rel'` are already the laws wanted, up to identifying the realizer's values
with `toFun`. `realizer_toFun` does that identification once, from the promoted positional reading
of the realizer together with the graph lemma, and both the arguments and the function's output go
through it.

`map_rel'` is an `iff`, so the relation law both preserves and reflects — which is what an
isomorphism of structures requires and an embedding-only argument would not give.

No structural law for the inverse map is proved: `ComputableStructureIsoIn` asks for the forward laws
and both inverse equations, and the inverse's laws follow from those (`symm` already does it).
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-! ### Stage bounds -/

/-- The least stage by which every argument has been matched. Vacuously `0` on no arguments. -/
def argsStage {n : ℕ} (v : Fin n → ℕ) : ℕ :=
  Finset.univ.sup fun k ↦ v k + 1

theorem le_argsStage {n : ℕ} (v : Fin n → ℕ) (k : Fin n) : v k + 1 ≤ argsStage v :=
  Finset.le_sup (f := fun k ↦ v k + 1) (Finset.mem_univ k)

@[simp] theorem argsStage_of_isEmpty {n : ℕ} (v : Fin n → ℕ) (h : n = 0) : argsStage v = 0 := by
  subst h
  simp [argsStage]

/-- The least stage by which every argument **and the value** have been matched. The second bound is
what the nullary case rests on: a constant has no arguments, so the argument bound is `0`. -/
def funStage (S : ComputableStructureIn O L) {n : ℕ} (f : L.Functions n) (v : Fin n → ℕ) : ℕ :=
  max (argsStage v) (@Structure.funMap L ℕ S.inst n f v + 1)

theorem le_funStage_of_arg (S : ComputableStructureIn O L) {n : ℕ} (f : L.Functions n)
    (v : Fin n → ℕ) (k : Fin n) : v k + 1 ≤ funStage S f v :=
  le_trans (le_argsStage v k) (le_max_left _ _)

theorem funMap_lt_funStage (S : ComputableStructureIn O L) {n : ℕ} (f : L.Functions n)
    (v : Fin n → ℕ) : @Structure.funMap L ℕ S.inst n f v + 1 ≤ funStage S f v :=
  le_max_right _ _

section Iso

variable {E : Set (ℕ →. ℕ)} {S T : ComputableStructureIn O L}
  (r : RepresentationCoverIn E S.canonicalAge T.canonicalAge)
  (rb : RepresentationCoverIn E T.canonicalAge S.canonicalAge)
  (H : ComputablyHomogeneousIn E T) (Hs : ComputablyHomogeneousIn E S)

namespace BackForthState

/-! ### Points of a matched stage -/

/-- A value matched by stage `N`, as a point of that stage's source member. Its own discovery
occurrence witnesses membership. -/
noncomputable def stagePoint {N v : ℕ} (h : v + 1 ≤ N) :
    (S.canonicalAge.memberAt (stateAt r rb H Hs N).tightMap.domIdx).domain :=
  ⟨v, by
    refine S.mem_canonicalAge_domainAt_of_mem_gens ?_
    rw [show allTupleFor (stateAt r rb H Hs N).tightMap.domIdx
      = (stateAt r rb H Hs N).sourceTuple from allTupleFor_encode _]
    exact List.mem_of_getElem? (sourceTuple_getElem?_two_mul_of_le r rb H Hs h)⟩

@[simp] theorem stagePoint_coe {N v : ℕ} (h : v + 1 ≤ N) :
    ((stagePoint r rb H Hs h : (S.canonicalAge.memberAt
      (stateAt r rb H Hs N).tightMap.domIdx).domain) : ℕ) = v := rfl

/-- **The stage realizer computes `toFun`.** At a matched stage, the realizer's value at any point
named by a recorded source entry is `toFun` of that entry.

The one bridge between the finite stages and the limit map: the positional reading of the realizer
says where the point goes *in the stage's target tuple*, and the graph lemma says that entry is
`toFun` of the source entry. Both the arguments and the output of a function application use it. -/
theorem realizer_toFun {N : ℕ}
    {f : (S.canonicalAge.memberAt (stateAt r rb H Hs N).tightMap.domIdx).domain ↪[L]
      (T.canonicalAge.memberAt (stateAt r rb H Hs N).tightMap.codIdx).domain}
    (hf : PartialAgeIn.PartialRealizesBetween S.canonicalAge T.canonicalAge
      (stateAt r rb H Hs N).tightMap f)
    {i : ℕ} {x : (S.canonicalAge.memberAt (stateAt r rb H Hs N).tightMap.domIdx).domain}
    (hx : (stateAt r rb H Hs N).sourceTuple[i]? = some (x : ℕ)) :
    ((f x : (T.canonicalAge.memberAt (stateAt r rb H Hs N).tightMap.codIdx).domain) : ℕ)
      = toFun r rb H Hs (x : ℕ) := by
  have hi : i < (stateAt r rb H Hs N).sourceTuple.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hx
    exact absurd hx (by simp)
  have hval : ((x : ℕ)) = (stateAt r rb H Hs N).sourceTuple[i] :=
    (Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hx)).symm
  have h1 := realizer_getElem? hf hi hval
  have h2 := targetTuple_getElem?_eq_toFun r rb H Hs hx
  exact (Option.some.inj (h1.symm.trans h2))

/-! ### The structure laws -/

/-- **The forward map commutes with function interpretation.** At `funStage`, every argument and the
value itself are matched, so all `n + 1` points live in the stage's source member and the realizer's
`map_fun'` is the law wanted. -/
theorem toFun_funMap {n : ℕ} (fs : L.Functions n) (v : Fin n → ℕ) :
    toFun r rb H Hs (@Structure.funMap L ℕ S.inst n fs v)
      = @Structure.funMap L ℕ T.inst n fs fun k ↦ toFun r rb H Hs (v k) := by
  obtain ⟨f, hf⟩ := stateAt_matched r rb H Hs (funStage S fs v)
  set x : Fin n → (S.canonicalAge.memberAt
      (stateAt r rb H Hs (funStage S fs v)).tightMap.domIdx).domain :=
    fun k ↦ stagePoint r rb H Hs (le_funStage_of_arg S fs v k) with hxdef
  have hxk : ∀ k, ((x k : (S.canonicalAge.memberAt
      (stateAt r rb H Hs (funStage S fs v)).tightMap.domIdx).domain) : ℕ) = v k := fun _ ↦ rfl
  -- the value, as a point of the same member
  have hout : @Structure.funMap L _ _ n fs x
      = stagePoint r rb H Hs (funMap_lt_funStage S fs v) := by
    refine Subtype.ext ?_
    show @Structure.funMap L ℕ S.inst n fs (fun k ↦ ((x k : _) : ℕ))
      = @Structure.funMap L ℕ S.inst n fs v
    exact congrArg _ (funext hxk)
  -- the arguments and the value both read through the same bridge
  have hargs : ∀ k, ((f (x k) : (T.canonicalAge.memberAt
      (stateAt r rb H Hs (funStage S fs v)).tightMap.codIdx).domain) : ℕ)
      = toFun r rb H Hs (v k) := fun k ↦
    realizer_toFun r rb H Hs hf
      (sourceTuple_getElem?_two_mul_of_le r rb H Hs (le_funStage_of_arg S fs v k))
  have hvalue : ((f (stagePoint r rb H Hs (funMap_lt_funStage S fs v)) :
      (T.canonicalAge.memberAt
        (stateAt r rb H Hs (funStage S fs v)).tightMap.codIdx).domain) : ℕ)
      = toFun r rb H Hs (@Structure.funMap L ℕ S.inst n fs v) :=
    realizer_toFun r rb H Hs hf
      (sourceTuple_getElem?_two_mul_of_le r rb H Hs (funMap_lt_funStage S fs v))
  rw [← hvalue, ← hout, HomClass.map_fun (L := L) f fs x]
  show @Structure.funMap L ℕ T.inst n fs (fun k ↦ ((f (x k) : _) : ℕ)) = _
  exact congrArg _ (funext hargs)

/-- **The forward map preserves and reflects relations.** `argsStage` suffices — a relation
application names no value beyond its arguments — and `map_rel'` is an `iff`, so both directions come
out at once. -/
theorem toFun_relMap {n : ℕ} (R : L.Relations n) (v : Fin n → ℕ) :
    @Structure.RelMap L ℕ T.inst n R (fun k ↦ toFun r rb H Hs (v k))
      ↔ @Structure.RelMap L ℕ S.inst n R v := by
  obtain ⟨f, hf⟩ := stateAt_matched r rb H Hs (argsStage v)
  set x : Fin n → (S.canonicalAge.memberAt
      (stateAt r rb H Hs (argsStage v)).tightMap.domIdx).domain :=
    fun k ↦ stagePoint r rb H Hs (le_argsStage v k) with hxdef
  have hargs : ∀ k, ((f (x k) : (T.canonicalAge.memberAt
      (stateAt r rb H Hs (argsStage v)).tightMap.codIdx).domain) : ℕ)
      = toFun r rb H Hs (v k) := fun k ↦
    realizer_toFun r rb H Hs hf
      (sourceTuple_getElem?_two_mul_of_le r rb H Hs (le_argsStage v k))
  have hrel := f.map_rel' R x
  rw [show (fun k ↦ toFun r rb H Hs (v k))
    = fun k ↦ ((f (x k) : (T.canonicalAge.memberAt
      (stateAt r rb H Hs (argsStage v)).tightMap.codIdx).domain) : ℕ)
    from funext fun k ↦ (hargs k).symm]
  exact hrel

end BackForthState

/-! ### The package -/

/-- **CHMM Proposition 3.2.** A computable isomorphism of representations between the canonical ages,
together with computable homogeneity of both structures, yields a computable isomorphism of the
structures themselves.

The two covers are pinned by direction: `r.forward` drives the forth half and the base case, and
`r.backward` drives the back half. The homogeneity selectors are pinned the same way — the forth half
consults the **target**'s, the back half the **source**'s. Nothing here assumes `O ⊆ E`. -/
noncomputable def backForthIso {E : Set (ℕ →. ℕ)} {S T : ComputableStructureIn O L}
    (r : RepresentationIsoIn E S.canonicalAge T.canonicalAge)
    (Hs : ComputablyHomogeneousIn E S) (Ht : ComputablyHomogeneousIn E T) :
    ComputableStructureIsoIn E S T where
  toFun := BackForthState.toFun r.forward r.backward Ht Hs
  invFun := BackForthState.invFun r.forward r.backward Ht Hs
  toFun_computableIn := BackForthState.toFun_computableIn r.forward r.backward Ht Hs
  invFun_computableIn := BackForthState.invFun_computableIn r.forward r.backward Ht Hs
  left_inv := BackForthState.invFun_toFun r.forward r.backward Ht Hs
  right_inv := BackForthState.toFun_invFun r.forward r.backward Ht Hs
  toFun_funMap := fun _ fs v ↦ BackForthState.toFun_funMap r.forward r.backward Ht Hs fs v
  toFun_relMap := fun _ R v ↦ BackForthState.toFun_relMap r.forward r.backward Ht Hs R v

@[simp] theorem backForthIso_toFun {E : Set (ℕ →. ℕ)} {S T : ComputableStructureIn O L}
    (r : RepresentationIsoIn E S.canonicalAge T.canonicalAge)
    (Hs : ComputablyHomogeneousIn E S) (Ht : ComputablyHomogeneousIn E T) :
    (backForthIso r Hs Ht).toFun = BackForthState.toFun r.forward r.backward Ht Hs := rfl

@[simp] theorem backForthIso_invFun {E : Set (ℕ →. ℕ)} {S T : ComputableStructureIn O L}
    (r : RepresentationIsoIn E S.canonicalAge T.canonicalAge)
    (Hs : ComputablyHomogeneousIn E S) (Ht : ComputablyHomogeneousIn E T) :
    (backForthIso r Hs Ht).invFun = BackForthState.invFun r.forward r.backward Ht Hs := rfl

end Iso

end FirstOrder.Language
