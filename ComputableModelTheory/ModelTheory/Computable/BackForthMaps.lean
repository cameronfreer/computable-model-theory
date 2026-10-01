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

* `toFun x` reads `targetTuple` at `ℓ + 2 * x` in `stateAt s₀ (x + 1)` — the position the forth half
  of round `x` put `x` at, on the source side;
* `invFun y` reads `sourceTuple` at `ℓ + 2 * y + 1` in `stateAt s₀ (y + 1)` — the position the back
  half of round `y` put `y` at, on the target side.

Here `ℓ` is the seed's length: `s₀.sourceTuple.length` for `toFun` and `s₀.targetTuple.length` for
`invFun`, which agree on a matched seed; from `empty` both are `0`.

**The two canonical positions differ, and must.** At stage `x + 1` the source tuple's entry at
`ℓ + 2 * x` is `x`, while its entry at `ℓ + 2 * x + 1` is whatever the back half's homogeneity
chose; the target tuple is the other way round. Reading both maps at one canonical position would
silently pair `x` with the wrong entry. Nothing below reads the source and target at the same
canonical index.

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

## The seed's coordinates are extended

The graph lemmas hold at stage `0` too, where the state is the seed itself. So every coordinate of
a matched seed is carried to its prescribed image by `toFun` (`toFun_extends`), repeated coordinates
included — which is the whole content of extending a prescribed match.

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
  (H : ComputablyHomogeneousIn E T) (Hs : ComputablyHomogeneousIn E S) (s₀ : BackForthState)

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
  (stateAt r rb H Hs s₀ (x + 1)).targetTuple[s₀.sourceTuple.length + 2 * x]!

/-- **The backward map.** At the stage where `y` was matched, the source entry at `y`'s own
position — a *different* canonical position from the forward map's. -/
noncomputable def invFun (y : ℕ) : ℕ :=
  (stateAt r rb H Hs s₀ (y + 1)).sourceTuple[s₀.targetTuple.length + 2 * y + 1]!

/-! ### The canonical lookups, and their persistence

The positions use each tuple's own seed length; comparing a position across the two tuples needs
the seed's two lengths to agree, which a matched seed supplies. -/

variable {s₀}

theorem toFun_getElem? (h₀ : s₀.Matched S T) (x : ℕ) :
    (stateAt r rb H Hs s₀ (x + 1)).targetTuple[s₀.sourceTuple.length + 2 * x]?
      = some (toFun r rb H Hs s₀ x) := by
  have hlen := length_eq_of_matched h₀
  have hlt : s₀.sourceTuple.length + 2 * x
      < (stateAt r rb H Hs s₀ (x + 1)).targetTuple.length := by
    rw [stateAt_targetTuple_length]; omega
  rw [List.getElem?_eq_getElem hlt, toFun,
    getElem!_pos (stateAt r rb H Hs s₀ (x + 1)).targetTuple _ hlt]

theorem invFun_getElem? (h₀ : s₀.Matched S T) (y : ℕ) :
    (stateAt r rb H Hs s₀ (y + 1)).sourceTuple[s₀.targetTuple.length + 2 * y + 1]?
      = some (invFun r rb H Hs s₀ y) := by
  have hlen := length_eq_of_matched h₀
  have hlt : s₀.targetTuple.length + 2 * y + 1
      < (stateAt r rb H Hs s₀ (y + 1)).sourceTuple.length := by
    rw [stateAt_sourceTuple_length]; omega
  rw [List.getElem?_eq_getElem hlt, invFun,
    getElem!_pos (stateAt r rb H Hs s₀ (y + 1)).sourceTuple _ hlt]

theorem toFun_getElem?_of_le (h₀ : s₀.Matched S T) {x m : ℕ} (h : x + 1 ≤ m) :
    (stateAt r rb H Hs s₀ m).targetTuple[s₀.sourceTuple.length + 2 * x]?
      = some (toFun r rb H Hs s₀ x) :=
  getElem?_of_prefix (stateAt_targetTuple_prefix r rb H Hs s₀ h) (toFun_getElem? r rb H Hs h₀ x)

theorem invFun_getElem?_of_le (h₀ : s₀.Matched S T) {y m : ℕ} (h : y + 1 ≤ m) :
    (stateAt r rb H Hs s₀ m).sourceTuple[s₀.targetTuple.length + 2 * y + 1]?
      = some (invFun r rb H Hs s₀ y) :=
  getElem?_of_prefix (stateAt_sourceTuple_prefix r rb H Hs s₀ h) (invFun_getElem? r rb H Hs h₀ y)

variable (s₀)

/-- The discovery occurrence of `x` on the source side, at every later stage. -/
theorem sourceTuple_getElem?_two_mul_of_le {x m : ℕ} (h : x + 1 ≤ m) :
    (stateAt r rb H Hs s₀ m).sourceTuple[s₀.sourceTuple.length + 2 * x]? = some x :=
  getElem?_of_prefix (stateAt_sourceTuple_prefix r rb H Hs s₀ h)
    (stateAt_sourceTuple_getElem?_two_mul r rb H Hs s₀ x)

/-- The discovery occurrence of `y` on the target side, at every later stage. -/
theorem targetTuple_getElem?_two_mul_succ_of_le {y m : ℕ} (h : y + 1 ≤ m) :
    (stateAt r rb H Hs s₀ m).targetTuple[s₀.targetTuple.length + 2 * y + 1]? = some y :=
  getElem?_of_prefix (stateAt_targetTuple_prefix r rb H Hs s₀ h)
    (stateAt_targetTuple_getElem?_two_mul_succ r rb H Hs s₀ y)

variable {s₀}

/-! ### The graph lemmas -/

/-- Both tuples of a stage have the same length on a matched seed, so an in-range source position is
an in-range target position. -/
private theorem lt_length_of_source_getElem? (h₀ : s₀.Matched S T) {m i x : ℕ}
    (hx : (stateAt r rb H Hs s₀ m).sourceTuple[i]? = some x) :
    i < (stateAt r rb H Hs s₀ m).targetTuple.length := by
  have hi : i < (stateAt r rb H Hs s₀ m).sourceTuple.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hx
    exact absurd hx (by simp)
  have hlen := length_eq_of_matched h₀
  rw [stateAt_targetTuple_length]
  rw [stateAt_sourceTuple_length] at hi
  omega

private theorem lt_length_of_target_getElem? (h₀ : s₀.Matched S T) {m i y : ℕ}
    (hy : (stateAt r rb H Hs s₀ m).targetTuple[i]? = some y) :
    i < (stateAt r rb H Hs s₀ m).sourceTuple.length := by
  have hi : i < (stateAt r rb H Hs s₀ m).targetTuple.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hy
    exact absurd hy (by simp)
  have hlen := length_eq_of_matched h₀
  rw [stateAt_sourceTuple_length]
  rw [stateAt_targetTuple_length] at hi
  omega

/-- **Every recorded source occurrence has target entry `toFun x`** — at any stage, at any position,
canonical or not, seed positions included.

The occurrence and the discovery occurrence are moved to `max m (x + 1)`, where they are two source
positions holding the same value in one matched state; coordinate consistency then equates the
target entries there, and the value comes back down because nothing is ever revised. -/
theorem targetTuple_getElem?_eq_toFun (h₀ : s₀.Matched S T) {m i x : ℕ}
    (hx : (stateAt r rb H Hs s₀ m).sourceTuple[i]? = some x) :
    (stateAt r rb H Hs s₀ m).targetTuple[i]? = some (toFun r rb H Hs s₀ x) := by
  have hmN : m ≤ max m (x + 1) := le_max_left _ _
  have hxN : x + 1 ≤ max m (x + 1) := le_max_right _ _
  have h1 : (stateAt r rb H Hs s₀ (max m (x + 1))).sourceTuple[i]? = some x :=
    getElem?_of_prefix (stateAt_sourceTuple_prefix r rb H Hs s₀ hmN) hx
  have h2 : (stateAt r rb H Hs s₀ (max m (x + 1))).sourceTuple[s₀.sourceTuple.length + 2 * x]?
      = some x :=
    sourceTuple_getElem?_two_mul_of_le r rb H Hs s₀ hxN
  have h3 : (stateAt r rb H Hs s₀ (max m (x + 1))).targetTuple[i]?
      = (stateAt r rb H Hs s₀ (max m (x + 1))).targetTuple[s₀.sourceTuple.length + 2 * x]? :=
    target_getElem?_eq_of_source_getElem?_eq
      (stateAt_matched r rb H Hs h₀ (max m (x + 1))) (h1.trans h2.symm)
  have hi := lt_length_of_source_getElem? r rb H Hs h₀ hx
  have h5 : (stateAt r rb H Hs s₀ (max m (x + 1))).targetTuple[i]?
      = some ((stateAt r rb H Hs s₀ m).targetTuple[i]) :=
    getElem?_of_prefix (stateAt_targetTuple_prefix r rb H Hs s₀ hmN)
      (List.getElem?_eq_getElem hi)
  rw [List.getElem?_eq_getElem hi]
  rw [h3, toFun_getElem?_of_le r rb H Hs h₀ hxN] at h5
  exact h5.symm

/-- **Every recorded target occurrence has source entry `invFun y`** — the mirror statement, proved
at `max m (y + 1)` from the other coordinate-consistency direction. -/
theorem sourceTuple_getElem?_eq_invFun (h₀ : s₀.Matched S T) {m i y : ℕ}
    (hy : (stateAt r rb H Hs s₀ m).targetTuple[i]? = some y) :
    (stateAt r rb H Hs s₀ m).sourceTuple[i]? = some (invFun r rb H Hs s₀ y) := by
  have hmN : m ≤ max m (y + 1) := le_max_left _ _
  have hyN : y + 1 ≤ max m (y + 1) := le_max_right _ _
  have h1 : (stateAt r rb H Hs s₀ (max m (y + 1))).targetTuple[i]? = some y :=
    getElem?_of_prefix (stateAt_targetTuple_prefix r rb H Hs s₀ hmN) hy
  have h2 : (stateAt r rb H Hs s₀ (max m (y + 1))).targetTuple[s₀.targetTuple.length + 2 * y + 1]?
      = some y :=
    targetTuple_getElem?_two_mul_succ_of_le r rb H Hs s₀ hyN
  have h3 : (stateAt r rb H Hs s₀ (max m (y + 1))).sourceTuple[i]?
      = (stateAt r rb H Hs s₀ (max m (y + 1))).sourceTuple[s₀.targetTuple.length + 2 * y + 1]? :=
    source_getElem?_eq_of_target_getElem?_eq
      (stateAt_matched r rb H Hs h₀ (max m (y + 1))) (h1.trans h2.symm)
  have hi := lt_length_of_target_getElem? r rb H Hs h₀ hy
  have h5 : (stateAt r rb H Hs s₀ (max m (y + 1))).sourceTuple[i]?
      = some ((stateAt r rb H Hs s₀ m).sourceTuple[i]) :=
    getElem?_of_prefix (stateAt_sourceTuple_prefix r rb H Hs s₀ hmN)
      (List.getElem?_eq_getElem hi)
  rw [List.getElem?_eq_getElem hi]
  rw [h3, invFun_getElem?_of_le r rb H Hs h₀ hyN] at h5
  exact h5.symm

/-! ### The seed is extended -/

/-- **`toFun` extends the seed**: every coordinate of a matched seed — repeated ones included — is
carried to its prescribed image. The graph lemma at stage `0`, where the state is the seed. -/
theorem toFun_extends (h₀ : s₀.Matched S T) {i x : ℕ} (hx : s₀.sourceTuple[i]? = some x) :
    s₀.targetTuple[i]? = some (toFun r rb H Hs s₀ x) :=
  targetTuple_getElem?_eq_toFun r rb H Hs h₀ (m := 0) hx

/-- **`invFun` extends the seed backwards.** -/
theorem invFun_extends (h₀ : s₀.Matched S T) {i y : ℕ} (hy : s₀.targetTuple[i]? = some y) :
    s₀.sourceTuple[i]? = some (invFun r rb H Hs s₀ y) :=
  sourceTuple_getElem?_eq_invFun r rb H Hs h₀ (m := 0) hy

/-! ### The inverse laws

Each is one canonical occurrence read through both graph lemmas. -/

theorem invFun_toFun (h₀ : s₀.Matched S T) (x : ℕ) :
    invFun r rb H Hs s₀ (toFun r rb H Hs s₀ x) = x := by
  have h := sourceTuple_getElem?_eq_invFun r rb H Hs h₀ (toFun_getElem? r rb H Hs h₀ x)
  rw [stateAt_sourceTuple_getElem?_two_mul r rb H Hs s₀ x] at h
  exact (Option.some.inj h).symm

theorem toFun_invFun (h₀ : s₀.Matched S T) (y : ℕ) :
    toFun r rb H Hs s₀ (invFun r rb H Hs s₀ y) = y := by
  have h := targetTuple_getElem?_eq_toFun r rb H Hs h₀ (invFun_getElem? r rb H Hs h₀ y)
  rw [stateAt_targetTuple_getElem?_two_mul_succ r rb H Hs s₀ y] at h
  exact (Option.some.inj h).symm

variable (s₀)

/-! ### Effectivity

Both maps are `stateAt` at a computed stage, projected and looked up at a computed position. The
oracle is the **map** oracle throughout; `O` is never consulted, and the seed and its lengths are
constants. -/

private theorem stage_computableIn :
    ComputableIn E fun x : ℕ ↦ stateAt r rb H Hs s₀ (x + 1) :=
  (stateAt_computableIn r rb H Hs s₀).comp ComputableIn.succ

private theorem offset_computableIn (c : ℕ) : ComputableIn E fun x : ℕ ↦ c + 2 * x :=
  (Primrec.nat_add.to_comp.computableIn₂).comp (ComputableIn.const c)
    ((Primrec.nat_mul.to_comp.computableIn₂).comp (ComputableIn.const 2) ComputableIn.id)

theorem toFun_computableIn : ComputableIn E (toFun r rb H Hs s₀) :=
  ((Primrec.list_getElem!.to_comp.computableIn₂).comp
    (targetTuple_computableIn.comp (stage_computableIn r rb H Hs s₀))
    (offset_computableIn s₀.sourceTuple.length)).of_eq fun _ ↦ rfl

theorem invFun_computableIn : ComputableIn E (invFun r rb H Hs s₀) :=
  ((Primrec.list_getElem!.to_comp.computableIn₂).comp
    (sourceTuple_computableIn.comp (stage_computableIn r rb H Hs s₀))
    (ComputableIn.succ.comp (offset_computableIn s₀.targetTuple.length))).of_eq fun _ ↦ rfl

end BackForthState

end Maps

end FirstOrder.Language
