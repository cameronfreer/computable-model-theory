/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.BackForthRun

/-!
# The total maps — CHMM Proposition 3.2, totality and the inverse laws

The run's two tuples, read as functions of `ℕ`. Each map looks at the stage where its argument was
first matched and reads the *other* tuple at the position where that happened:

* `toFun x` reads `targetTuple` at `2 * x` in `stateAt (x + 1)` — the position the forth half of
  round `x` put `x` at, on the source side;
* `invFun y` reads `sourceTuple` at `2 * y + 1` in `stateAt (y + 1)` — the position the back half of
  round `y` put `y` at, on the target side.

**The two canonical positions differ, and must.** At stage `x + 1` the source tuple's entry at
`2 * x` is `x`, while its entry at `2 * x + 1` is whatever the back half's homogeneity chose; the
target tuple is the other way round. Reading both maps at one canonical position would silently pair
`x` with the wrong entry. Nothing below reads the source and target at the same canonical index.

## Repeated coordinates are handled by moving up, not by scheduling

The load-bearing statements are the two *graph* lemmas: at **any** stage and **any** position, a
recorded source entry `x` has target entry `toFun x`, and a recorded target entry `y` has source
entry `invFun y`. Neither assumes the occurrence is the canonical one — a state may record the same
point many times, and the run never deduplicates.

Both are proved the same way: move the arbitrary occurrence and the canonical discovery occurrence
to a common later stage `max m (x + 1)`, where they are two occurrences of the same value in one
matched state, and apply the coordinate-consistency theorem there. That is exactly what those
theorems were stated globally for. No scheduling argument is needed, and neither is any claim that
occurrences are unique.

The inverse laws then follow by applying both graph lemmas to a single canonical occurrence.

Structure preservation is a separate landing: the function law needs a stage containing all
arguments *and* the output, the relation law only the arguments, and that finite-stage bookkeeping
does not belong here.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

section Maps

variable {E : Set (ℕ →. ℕ)} {S T : ComputableStructureIn O L}
  (r : RepresentationCoverIn E S.canonicalAge T.canonicalAge)
  (rb : RepresentationCoverIn E T.canonicalAge S.canonicalAge)
  (H : ComputablyHomogeneousIn E T) (Hs : ComputablyHomogeneousIn E S)

namespace BackForthState

/-- Lookups survive prefix extension. The one piece of list arithmetic in this module; everything
else moves values between stages through it. -/
private theorem getElem?_of_prefix {a b : Tuple ℕ} (hab : a <+: b) {i x : ℕ}
    (h : a[i]? = some x) : b[i]? = some x := by
  obtain ⟨t, rfl⟩ := hab
  have hi : i < a.length := by
    by_contra hi
    rw [List.getElem?_eq_none (by omega)] at h
    exact absurd h (by simp)
  rw [List.getElem?_append_left hi]
  exact h

/-! ### The two maps -/

/-- **The forward map.** At the stage where `x` was matched, the target entry at `x`'s own
position. -/
noncomputable def toFun (x : ℕ) : ℕ :=
  (stateAt r rb H Hs (x + 1)).targetTuple[2 * x]!

/-- **The backward map.** At the stage where `y` was matched, the source entry at `y`'s own
position — a *different* canonical position from the forward map's. -/
noncomputable def invFun (y : ℕ) : ℕ :=
  (stateAt r rb H Hs (y + 1)).sourceTuple[2 * y + 1]!

/-! ### The canonical lookups, and their persistence -/

theorem toFun_getElem? (x : ℕ) :
    (stateAt r rb H Hs (x + 1)).targetTuple[2 * x]? = some (toFun r rb H Hs x) := by
  have hlt : 2 * x < (stateAt r rb H Hs (x + 1)).targetTuple.length := by
    rw [stateAt_targetTuple_length]; omega
  rw [List.getElem?_eq_getElem hlt, toFun,
    getElem!_pos (stateAt r rb H Hs (x + 1)).targetTuple (2 * x) hlt]

theorem invFun_getElem? (y : ℕ) :
    (stateAt r rb H Hs (y + 1)).sourceTuple[2 * y + 1]? = some (invFun r rb H Hs y) := by
  have hlt : 2 * y + 1 < (stateAt r rb H Hs (y + 1)).sourceTuple.length := by
    rw [stateAt_sourceTuple_length]; omega
  rw [List.getElem?_eq_getElem hlt, invFun,
    getElem!_pos (stateAt r rb H Hs (y + 1)).sourceTuple (2 * y + 1) hlt]

theorem toFun_getElem?_of_le {x m : ℕ} (h : x + 1 ≤ m) :
    (stateAt r rb H Hs m).targetTuple[2 * x]? = some (toFun r rb H Hs x) :=
  getElem?_of_prefix (stateAt_targetTuple_prefix r rb H Hs h) (toFun_getElem? r rb H Hs x)

theorem invFun_getElem?_of_le {y m : ℕ} (h : y + 1 ≤ m) :
    (stateAt r rb H Hs m).sourceTuple[2 * y + 1]? = some (invFun r rb H Hs y) :=
  getElem?_of_prefix (stateAt_sourceTuple_prefix r rb H Hs h) (invFun_getElem? r rb H Hs y)

/-- The discovery occurrence of `x` on the source side, at every later stage. -/
theorem sourceTuple_getElem?_two_mul_of_le {x m : ℕ} (h : x + 1 ≤ m) :
    (stateAt r rb H Hs m).sourceTuple[2 * x]? = some x :=
  getElem?_of_prefix (stateAt_sourceTuple_prefix r rb H Hs h)
    (stateAt_sourceTuple_getElem?_two_mul r rb H Hs x)

/-- The discovery occurrence of `y` on the target side, at every later stage. -/
theorem targetTuple_getElem?_two_mul_succ_of_le {y m : ℕ} (h : y + 1 ≤ m) :
    (stateAt r rb H Hs m).targetTuple[2 * y + 1]? = some y :=
  getElem?_of_prefix (stateAt_targetTuple_prefix r rb H Hs h)
    (stateAt_targetTuple_getElem?_two_mul_succ r rb H Hs y)

/-! ### The graph lemmas -/

/-- Both tuples of a stage have the same length, so an in-range source position is an in-range
target position. -/
private theorem lt_length_of_source_getElem? {m i x : ℕ}
    (hx : (stateAt r rb H Hs m).sourceTuple[i]? = some x) :
    i < (stateAt r rb H Hs m).targetTuple.length := by
  have hi : i < (stateAt r rb H Hs m).sourceTuple.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hx
    exact absurd hx (by simp)
  rw [stateAt_targetTuple_length]
  rwa [stateAt_sourceTuple_length] at hi

private theorem lt_length_of_target_getElem? {m i y : ℕ}
    (hy : (stateAt r rb H Hs m).targetTuple[i]? = some y) :
    i < (stateAt r rb H Hs m).sourceTuple.length := by
  have hi : i < (stateAt r rb H Hs m).targetTuple.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hy
    exact absurd hy (by simp)
  rw [stateAt_sourceTuple_length]
  rwa [stateAt_targetTuple_length] at hi

/-- **Every recorded source occurrence has target entry `toFun x`** — at any stage, at any position,
canonical or not.

The occurrence and the discovery occurrence are moved to `max m (x + 1)`, where they are two source
positions holding the same value in one matched state; coordinate consistency then equates the target
entries there, and the value comes back down because nothing is ever revised. -/
theorem targetTuple_getElem?_eq_toFun {m i x : ℕ}
    (hx : (stateAt r rb H Hs m).sourceTuple[i]? = some x) :
    (stateAt r rb H Hs m).targetTuple[i]? = some (toFun r rb H Hs x) := by
  have hmN : m ≤ max m (x + 1) := le_max_left _ _
  have hxN : x + 1 ≤ max m (x + 1) := le_max_right _ _
  have h1 : (stateAt r rb H Hs (max m (x + 1))).sourceTuple[i]? = some x :=
    getElem?_of_prefix (stateAt_sourceTuple_prefix r rb H Hs hmN) hx
  have h2 : (stateAt r rb H Hs (max m (x + 1))).sourceTuple[2 * x]? = some x :=
    sourceTuple_getElem?_two_mul_of_le r rb H Hs hxN
  have h3 : (stateAt r rb H Hs (max m (x + 1))).targetTuple[i]?
      = (stateAt r rb H Hs (max m (x + 1))).targetTuple[2 * x]? :=
    target_getElem?_eq_of_source_getElem?_eq
      (stateAt_matched r rb H Hs (max m (x + 1))) (h1.trans h2.symm)
  have hi := lt_length_of_source_getElem? r rb H Hs hx
  have h5 : (stateAt r rb H Hs (max m (x + 1))).targetTuple[i]?
      = some ((stateAt r rb H Hs m).targetTuple[i]) :=
    getElem?_of_prefix (stateAt_targetTuple_prefix r rb H Hs hmN) (List.getElem?_eq_getElem hi)
  rw [List.getElem?_eq_getElem hi]
  rw [h3, toFun_getElem?_of_le r rb H Hs hxN] at h5
  exact h5.symm

/-- **Every recorded target occurrence has source entry `invFun y`** — the mirror statement, proved
at `max m (y + 1)` from the other coordinate-consistency direction. -/
theorem sourceTuple_getElem?_eq_invFun {m i y : ℕ}
    (hy : (stateAt r rb H Hs m).targetTuple[i]? = some y) :
    (stateAt r rb H Hs m).sourceTuple[i]? = some (invFun r rb H Hs y) := by
  have hmN : m ≤ max m (y + 1) := le_max_left _ _
  have hyN : y + 1 ≤ max m (y + 1) := le_max_right _ _
  have h1 : (stateAt r rb H Hs (max m (y + 1))).targetTuple[i]? = some y :=
    getElem?_of_prefix (stateAt_targetTuple_prefix r rb H Hs hmN) hy
  have h2 : (stateAt r rb H Hs (max m (y + 1))).targetTuple[2 * y + 1]? = some y :=
    targetTuple_getElem?_two_mul_succ_of_le r rb H Hs hyN
  have h3 : (stateAt r rb H Hs (max m (y + 1))).sourceTuple[i]?
      = (stateAt r rb H Hs (max m (y + 1))).sourceTuple[2 * y + 1]? :=
    source_getElem?_eq_of_target_getElem?_eq
      (stateAt_matched r rb H Hs (max m (y + 1))) (h1.trans h2.symm)
  have hi := lt_length_of_target_getElem? r rb H Hs hy
  have h5 : (stateAt r rb H Hs (max m (y + 1))).sourceTuple[i]?
      = some ((stateAt r rb H Hs m).sourceTuple[i]) :=
    getElem?_of_prefix (stateAt_sourceTuple_prefix r rb H Hs hmN) (List.getElem?_eq_getElem hi)
  rw [List.getElem?_eq_getElem hi]
  rw [h3, invFun_getElem?_of_le r rb H Hs hyN] at h5
  exact h5.symm

/-! ### The inverse laws

Each is one canonical occurrence read through both graph lemmas. -/

theorem invFun_toFun (x : ℕ) : invFun r rb H Hs (toFun r rb H Hs x) = x := by
  have h := sourceTuple_getElem?_eq_invFun r rb H Hs (toFun_getElem? r rb H Hs x)
  rw [stateAt_sourceTuple_getElem?_two_mul r rb H Hs x] at h
  exact (Option.some.inj h).symm

theorem toFun_invFun (y : ℕ) : toFun r rb H Hs (invFun r rb H Hs y) = y := by
  have h := targetTuple_getElem?_eq_toFun r rb H Hs (invFun_getElem? r rb H Hs y)
  rw [stateAt_targetTuple_getElem?_two_mul_succ r rb H Hs y] at h
  exact (Option.some.inj h).symm

/-! ### Effectivity

Both maps are `stateAt` at a computed stage, projected and looked up. The oracle is the **map**
oracle throughout; `O` is never consulted. -/

private theorem stage_computableIn :
    ComputableIn E fun x : ℕ ↦ stateAt r rb H Hs (x + 1) :=
  (stateAt_computableIn r rb H Hs).comp ComputableIn.succ

private theorem two_mul_computableIn : ComputableIn E fun x : ℕ ↦ 2 * x :=
  (Primrec.nat_mul.to_comp.computableIn₂).comp (ComputableIn.const 2) ComputableIn.id

theorem toFun_computableIn : ComputableIn E (toFun r rb H Hs) :=
  ((Primrec.list_getElem!.to_comp.computableIn₂).comp
    (targetTuple_computableIn.comp (stage_computableIn r rb H Hs))
    (two_mul_computableIn)).of_eq fun _ ↦ rfl

theorem invFun_computableIn : ComputableIn E (invFun r rb H Hs) :=
  ((Primrec.list_getElem!.to_comp.computableIn₂).comp
    (sourceTuple_computableIn.comp (stage_computableIn r rb H Hs))
    (ComputableIn.succ.comp (two_mul_computableIn))).of_eq fun _ ↦ rfl

end BackForthState

end Maps

end FirstOrder.Language
