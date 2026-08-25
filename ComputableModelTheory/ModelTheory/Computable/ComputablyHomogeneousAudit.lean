/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.ComputablyHomogeneous
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: computable homogeneity

Three obligations, and the first is the one that catches a **wrong reading** rather than a wrong
proof.

**Direction.** `h` inverts `g`, so `extensionMap`'s range tuple is `domainTuple ++ [y]`. The
plausible misreadings — `h` extending `g` forward, or `h` applying `g` a second time — produce
`imageTuple ++ [y]` and `g(g(d⃗)) ++ [y]`, and **both typecheck**, since all three are maps between
the same two members. The fixture is therefore a **three-cycle** and not a transposition: on an
involution `g ∘ g` is the identity, so the twice-applied misreading would coincide with the correct
answer and the row would pass by accident. On a three-cycle all three tuples are distinct, and
`test_direction_three_cycle` separates them.

This row needs no structure at all — `extensionMap` is pure query/answer data, so the encoding is
gated independently of any semantics.

**Malformed input.** A query whose `domainTuple` and `imageTuple` have different lengths is
**valid input**: it still receives both unconditional guarantees, and only `extension_actual`
becomes vacuous. `test_malformed_antecedent_is_false` shows the vacuity is genuine and comes for
free — `PartialRealizes` carries the length equation as a field, so no guard was needed and none
should be added.

**The empty tuple.** `D_[]` is a real member of `𝕂_𝒟` — `allTupleFor` hits `[]`, and `PartialAgeIn`
is empty-capable precisely so that this member exists. `test_empty_query_is_not_vacuous` goes
further than accepting the query: it shows the empty query's antecedent is *satisfiable*, so
`extension_actual` there is a real obligation rather than a second vacuous case.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

/-! ### Direction: the three-cycle -/

/-- `g` is the three-cycle `0 ↦ 1 ↦ 2 ↦ 0` on the recorded generators, with a fresh point `3`. -/
def dirQuery : HomogeneityQueryData :=
  ⟨[0, 1, 2], [1, 2, 0], 3⟩

/-- An answer; only its `imageOfNewPoint` matters below. -/
def dirAnswer : HomogeneityAnswerData :=
  ⟨[0, 1, 2, 3], 9⟩

/-- `g` really is the three-cycle: not the identity, and **not an involution**. -/
theorem test_g_is_a_three_cycle :
    dirQuery.originalMap.rangeTuple = [1, 2, 0] ∧
      dirQuery.originalMap.rangeTuple ≠ dirQuery.domainTuple :=
  ⟨rfl, by decide⟩

/-- **`h` inverts `g`.** The extension map runs out of `imageTuple ++ [newPoint]` and reports
`domainTuple ++ [imageOfNewPoint]`.

The two misreadings are separated explicitly. `[1, 2, 0, 9]` is `h` extending `g` *forward*;
`[2, 0, 1, 9]` is `g` applied twice. On a transposition the second would equal the correct answer,
which is why the fixture is a three-cycle. -/
theorem test_direction_three_cycle :
    (dirQuery.extensionMap dirAnswer).domIdx = encode ([1, 2, 0] ++ [3]) ∧
      (dirQuery.extensionMap dirAnswer).rangeTuple = [0, 1, 2, 9] ∧
        (dirQuery.extensionMap dirAnswer).rangeTuple ≠ [1, 2, 0, 9] ∧
          (dirQuery.extensionMap dirAnswer).rangeTuple ≠ [2, 0, 1, 9] :=
  ⟨rfl, rfl, by decide, by decide⟩

/-- And the source of `h` is the *image* tuple extended by the new point, not the domain tuple —
the other half of the same reversal. -/
theorem test_extension_source_is_the_image :
    (dirQuery.extensionMap dirAnswer).domIdx ≠ encode ([0, 1, 2] ++ [3]) := by
  simp only [HomogeneityQueryData.extensionMap_domIdx, dirQuery]
  exact fun h ↦ by simpa using congrArg (Denumerable.ofNat (List ℕ)) h

section Structure

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable (S : ComputableStructureIn O L)

/-! ### Malformed input -/

/-- Two generators, one image: not a map at all. -/
def malformedQuery : HomogeneityQueryData :=
  ⟨[0, 1], [5], 7⟩

/-- **The antecedent is false, for free.** `PartialRealizes` carries the length equation as a
field, so a length mismatch makes `extension_actual` vacuous with no guard anywhere in the
interface — which is why no guard should be added. -/
theorem test_malformed_antecedent_is_false :
    ¬ S.canonicalAge.PartialIsEmbedding malformedQuery.originalMap := by
  rintro ⟨-, hlen, -⟩
  rw [HomogeneityQueryData.originalMap_domIdx, HomogeneityQueryData.originalMap_rangeTuple,
    S.canonicalAge_gens, allTupleFor_encode] at hlen
  exact absurd hlen (by decide)

/-- **But it is still a valid query**: both unconditional guarantees apply to it unchanged. This
row typechecks only because neither clause is guarded. -/
theorem test_malformed_still_gets_both_guarantees (H : ComputablyHomogeneousIn E S) :
    S.canonicalAge.domainAt (encode malformedQuery.domainTuple)
        ⊆ S.canonicalAge.domainAt (encode (H.select malformedQuery).extensionTuple) ∧
      (H.select malformedQuery).imageOfNewPoint
        ∈ S.canonicalAge.domainAt (encode (H.select malformedQuery).extensionTuple) :=
  ⟨H.extends_domain malformedQuery, H.imageOfNewPoint_mem malformedQuery⟩

/-! ### The empty tuple -/

/-- The empty query: no generators, no images, one new point. -/
def emptyQuery : HomogeneityQueryData :=
  ⟨[], [], 0⟩

/-- **`D_[]` is a real member of `𝕂_𝒟`.** `allTupleFor` hits `[]`, and `PartialAgeIn` is
empty-capable precisely so that this member exists. -/
theorem test_empty_member_exists :
    S.canonicalAge.gens (encode ([] : Tuple ℕ)) = [] :=
  allTupleFor_encode []

/-- The empty query receives both unconditional guarantees like any other. -/
theorem test_empty_gets_both_guarantees (H : ComputablyHomogeneousIn E S) :
    S.canonicalAge.domainAt (encode emptyQuery.domainTuple)
        ⊆ S.canonicalAge.domainAt (encode (H.select emptyQuery).extensionTuple) ∧
      (H.select emptyQuery).imageOfNewPoint
        ∈ S.canonicalAge.domainAt (encode (H.select emptyQuery).extensionTuple) :=
  ⟨H.extends_domain emptyQuery, H.imageOfNewPoint_mem emptyQuery⟩

/-- **And its antecedent is satisfiable**, so `extension_actual` at the empty query is a real
obligation rather than a second vacuous case: the empty map is realized by the identity embedding,
whose coordinate condition is vacuous over `Fin 0`. -/
theorem test_empty_query_is_not_vacuous :
    S.canonicalAge.PartialIsEmbedding emptyQuery.originalMap := by
  refine ⟨PartialAgeIn.memberEmbedding rfl (Set.Subset.refl _), ?_, ?_⟩
  · show (S.canonicalAge.gens (encode ([] : Tuple ℕ))).length = ([] : Tuple ℕ).length
    rw [S.canonicalAge_gens, allTupleFor_encode]
  · intro k
    have hgens : S.canonicalAge.gens emptyQuery.originalMap.domIdx = [] :=
      allTupleFor_encode []
    have hzero : (S.canonicalAge.gens emptyQuery.originalMap.domIdx).length = 0 := by
      rw [hgens]; rfl
    exact (Fin.cast hzero k).elim0

end Structure

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.test_g_is_a_three_cycle
#assert_standard_axioms FirstOrder.Language.test_direction_three_cycle
#assert_standard_axioms FirstOrder.Language.test_extension_source_is_the_image
#assert_standard_axioms FirstOrder.Language.test_malformed_antecedent_is_false
#assert_standard_axioms FirstOrder.Language.test_malformed_still_gets_both_guarantees
#assert_standard_axioms FirstOrder.Language.test_empty_member_exists
#assert_standard_axioms FirstOrder.Language.test_empty_gets_both_guarantees
#assert_standard_axioms FirstOrder.Language.test_empty_query_is_not_vacuous
