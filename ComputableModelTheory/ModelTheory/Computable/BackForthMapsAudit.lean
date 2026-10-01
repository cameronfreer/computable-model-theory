/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.BackForthMaps
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: the total maps

**The two canonical positions are different, and each map reads the other tuple.**
`test_canonical_positions` pairs each lookup with the discovery occurrence it belongs to: `toFun x`
is the *target* entry at `2 * x`, where the source entry is `x`; `invFun y` is the *source* entry at
`2 * y + 1`, where the target entry is `y`. The final conjunct records that the two canonical
indices have different parities. A version of either map reading at the other's position would break
the pairing silently, and this is the row that would catch it.

**Occurrences need not be canonical, or unique.** `test_repeated_occurrence` takes two source
occurrences of the same `x` — at *different positions and different stages*, with no uniqueness
hypothesis — and gets `toFun x` at both. The run never deduplicates, so this is the situation the
graph lemmas actually meet; they handle it by moving to a common later stage rather than by any
scheduling argument.

**Both inverse laws**, from `test_inverse_laws`. Each is one canonical occurrence read through both
graph lemmas.

**Effectivity with `O` and `E` unrelated.** `test_maps_computable_no_inclusion` states both
computability facts with two covers and two homogeneity selectors at an arbitrary `E`, structures
presented at `O`, and no hypothesis relating them.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

section Maps

variable {E : Set (ℕ →. ℕ)} {S T : ComputableStructureIn O L}
  (r : RepresentationCoverIn E S.canonicalAge T.canonicalAge)
  (rb : RepresentationCoverIn E T.canonicalAge S.canonicalAge)
  (H : ComputablyHomogeneousIn E T) (Hs : ComputablyHomogeneousIn E S)

/-- **Each map reads the other tuple, at its own canonical position** — Proposition 3.2's positions,
at the empty seed. The first two conjuncts pair the forward map with the source discovery of `x` at
`2 * x`; the next two pair the backward map with the target discovery of `y` at `2 * y + 1`. The
last records that the two canonical positions differ in parity, so neither map could be read at the
other's index. -/
theorem test_canonical_positions (x y : ℕ) :
    (BackForthState.stateAt r rb H Hs BackForthState.empty (x + 1)).sourceTuple[2 * x]? = some x ∧
      (BackForthState.stateAt r rb H Hs BackForthState.empty (x + 1)).targetTuple[2 * x]?
          = some (BackForthState.toFun r rb H Hs BackForthState.empty x) ∧
        (BackForthState.stateAt r rb H Hs BackForthState.empty (y + 1)).targetTuple[2 * y + 1]?
            = some y ∧
          (BackForthState.stateAt r rb H Hs BackForthState.empty (y + 1)).sourceTuple[2 * y + 1]?
              = some (BackForthState.invFun r rb H Hs BackForthState.empty y) ∧
            2 * x ≠ 2 * x + 1 := by
  have h₀ := BackForthState.empty_matched (S := S) (T := T) r
  have e1 := BackForthState.stateAt_sourceTuple_getElem?_two_mul r rb H Hs BackForthState.empty x
  have e2 := BackForthState.toFun_getElem? r rb H Hs h₀ x
  have e3 := BackForthState.stateAt_targetTuple_getElem?_two_mul_succ r rb H Hs
    BackForthState.empty y
  have e4 := BackForthState.invFun_getElem? r rb H Hs h₀ y
  simp only [BackForthState.empty_sourceTuple, BackForthState.empty_targetTuple, List.length_nil,
    zero_add] at e1 e2 e3 e4
  exact ⟨e1, e2, e3, e4, by omega⟩

/-- **Repeated occurrences are handled by moving up**: two source occurrences of the same `x` — at
any stages, any positions, seed positions included, neither assumed canonical, neither assumed
unique — both have target entry `toFun x`. -/
theorem test_repeated_occurrence {s₀ : BackForthState} (h₀ : s₀.Matched S T) {m m' i j x : ℕ}
    (hi : (BackForthState.stateAt r rb H Hs s₀ m).sourceTuple[i]? = some x)
    (hj : (BackForthState.stateAt r rb H Hs s₀ m').sourceTuple[j]? = some x) :
    (BackForthState.stateAt r rb H Hs s₀ m).targetTuple[i]?
        = some (BackForthState.toFun r rb H Hs s₀ x) ∧
      (BackForthState.stateAt r rb H Hs s₀ m').targetTuple[j]?
        = some (BackForthState.toFun r rb H Hs s₀ x) :=
  ⟨BackForthState.targetTuple_getElem?_eq_toFun r rb H Hs h₀ hi,
    BackForthState.targetTuple_getElem?_eq_toFun r rb H Hs h₀ hj⟩

/-- The mirror: two target occurrences of the same `y` both have source entry `invFun y`. -/
theorem test_repeated_occurrence_target {s₀ : BackForthState} (h₀ : s₀.Matched S T)
    {m m' i j y : ℕ}
    (hi : (BackForthState.stateAt r rb H Hs s₀ m).targetTuple[i]? = some y)
    (hj : (BackForthState.stateAt r rb H Hs s₀ m').targetTuple[j]? = some y) :
    (BackForthState.stateAt r rb H Hs s₀ m).sourceTuple[i]?
        = some (BackForthState.invFun r rb H Hs s₀ y) ∧
      (BackForthState.stateAt r rb H Hs s₀ m').sourceTuple[j]?
        = some (BackForthState.invFun r rb H Hs s₀ y) :=
  ⟨BackForthState.sourceTuple_getElem?_eq_invFun r rb H Hs h₀ hi,
    BackForthState.sourceTuple_getElem?_eq_invFun r rb H Hs h₀ hj⟩

/-- **The seed is extended**, both ways: each seed coordinate goes to its prescribed image under
`toFun`, and back under `invFun` — the graph lemmas at stage `0`. -/
theorem test_seed_extended {s₀ : BackForthState} (h₀ : s₀.Matched S T) {i x y : ℕ}
    (hx : s₀.sourceTuple[i]? = some x) (hy : s₀.targetTuple[i]? = some y) :
    s₀.targetTuple[i]? = some (BackForthState.toFun r rb H Hs s₀ x) ∧
      s₀.sourceTuple[i]? = some (BackForthState.invFun r rb H Hs s₀ y) :=
  ⟨BackForthState.toFun_extends r rb H Hs h₀ hx, BackForthState.invFun_extends r rb H Hs h₀ hy⟩

/-- **Both inverse laws**, from any matched seed. -/
theorem test_inverse_laws {s₀ : BackForthState} (h₀ : s₀.Matched S T) :
    (∀ x, BackForthState.invFun r rb H Hs s₀ (BackForthState.toFun r rb H Hs s₀ x) = x) ∧
      ∀ y, BackForthState.toFun r rb H Hs s₀ (BackForthState.invFun r rb H Hs s₀ y) = y :=
  ⟨BackForthState.invFun_toFun r rb H Hs h₀, BackForthState.toFun_invFun r rb H Hs h₀⟩

/-- Consequences of the two inverse laws, recorded because the isomorphism interface will ask for
them: the forward map is a bijection. -/
theorem test_toFun_bijective {s₀ : BackForthState} (h₀ : s₀.Matched S T) :
    Function.Bijective (BackForthState.toFun r rb H Hs s₀) :=
  ⟨Function.LeftInverse.injective (BackForthState.invFun_toFun r rb H Hs h₀),
    Function.RightInverse.surjective (BackForthState.toFun_invFun r rb H Hs h₀)⟩

/-- **Both maps are computable in the map oracle**, with `E` unrelated to `O`, for any seed. -/
theorem test_maps_computable_no_inclusion (s₀ : BackForthState) :
    ComputableIn E (BackForthState.toFun r rb H Hs s₀) ∧
      ComputableIn E (BackForthState.invFun r rb H Hs s₀) :=
  ⟨BackForthState.toFun_computableIn r rb H Hs s₀,
    BackForthState.invFun_computableIn r rb H Hs s₀⟩

end Maps

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.test_canonical_positions
#assert_standard_axioms FirstOrder.Language.test_repeated_occurrence
#assert_standard_axioms FirstOrder.Language.test_repeated_occurrence_target
#assert_standard_axioms FirstOrder.Language.test_seed_extended
#assert_standard_axioms FirstOrder.Language.test_inverse_laws
#assert_standard_axioms FirstOrder.Language.test_toFun_bijective
#assert_standard_axioms FirstOrder.Language.test_maps_computable_no_inclusion
