/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.CanonicalCAP
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: CAP for the canonical age of a computably homogeneous structure

Five obligations, and the two halves of the closing realizer are gated **separately** on purpose.

**Totality and effectivity.** `test_selector_total_and_effective` records both: the selector is
`RecursiveIn E`, and it halts on *every* span — stronger than `PartialCAPIn`'s carrier-validity
clause asks. `E` is unrelated to `O` throughout, and no inclusion appears in any binder.

**Malformed input.** `test_malformed_unconditional` takes an **arbitrary** span, with no actualness
and no carrier validity, and reads back all three unconditional clauses. That is the clause split
`CAPWitnessIn` was introduced for, and this row is what would fail if the left leg were ever built
from the span's range tuple instead of the left member's own generators.

**The two halves.** `test_offset_behaviour` and `test_prefix_behaviour` expose the same realizer's
two readings. The offset one gives the right leg its coordinates; the prefix one makes the square
commute. A refactor that preserved right actualness while breaking the square would pass the first
and fail the second — which is exactly why they are not bundled.

**The empty-generator boundary.** When the right member records no generators the fold does nothing:
`chosen` is empty and the apex is the left member's generators unchanged. Gated without a fixture,
from the length equation.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
  {F : ComputableStructureIn O L} (H : ComputablyHomogeneousIn E F)

/-! ### Totality and effectivity -/

/-- **Total and computable in the map oracle.** The selector is `RecursiveIn E`; it converges on
every span, not only carrier-valid ones; and `O` is never consulted — no inclusion between the two
oracles appears in the binders or the proof. -/
theorem test_selector_total_and_effective :
    RecursiveIn E (fun S : PotentialSpanData ↦ Part.some (H.capSelect S)) ∧
      ComputableIn E H.capSelect ∧
        ∀ S : PotentialSpanData, (Part.some (H.capSelect S)).Dom :=
  ⟨H.capSelect_recursiveIn, H.capSelect_computableIn, fun _ ↦ trivial⟩

/-- Each joint of the chain is separately computable. -/
theorem test_chain_computable :
    ComputableIn E H.capFold ∧ ComputableIn E H.capChosen ∧ ComputableIn E H.capApex ∧
      ComputableIn E H.capLeft ∧ ComputableIn E H.capRight :=
  ⟨H.capFold_computableIn, H.capChosen_computableIn, H.capApex_computableIn,
    H.capLeft_computableIn, H.capRight_computableIn⟩

/-! ### Malformed input -/

/-- **All three unconditional clauses, on an arbitrary span.** No actualness, no carrier validity,
no well-shapedness of the input. -/
theorem test_malformed_unconditional (S : PotentialSpanData) :
    (H.capSelect S).WellShapedFor S ∧
      F.canonicalAge.PartialIsEmbedding (H.capSelect S).leftToApex ∧
        F.canonicalAge.PartialWellFormed (H.capSelect S).rightToApex :=
  ⟨H.capSelect_wellShaped S, H.capLeft_isEmbedding S, H.capRight_wellFormed S⟩

/-- The apex is the **left member's own recorded generators** followed by the chosen images — the
shape the unconditional left clause depends on. -/
theorem test_apex_shape (S : PotentialSpanData) :
    H.capApex S = allTupleFor S.left.codIdx ++ H.capChosen S ∧
      (H.capLeft S).rangeTuple = allTupleFor S.left.codIdx ∧
        (H.capRight S).rangeTuple = H.capChosen S :=
  ⟨rfl, rfl, rfl⟩

/-! ### The two halves of the closing realizer -/

/-- **The offset half.** One realizer whose `PartialRealizesAt` conjunct sends the right member's
recorded generators onto `capChosen` — this is what makes the right leg actual. -/
theorem test_offset_behaviour {S : PotentialSpanData}
    (hact : F.canonicalAge.PartialSpanActual S) :
    ∃ g, F.canonicalAge.PartialRealizesAt (H.capRight S) S.right.codIdx
      (encode (H.capApex S)) g :=
  ⟨_, (H.exists_closingRealizer hact).choose_spec.1⟩

/-- **The prefix half**, on the *same* realizer: the old right span range goes to the old left span
range, positionally. Bundling the two readings would let a refactor keep actualness while breaking
the square. -/
theorem test_prefix_behaviour {S : PotentialSpanData}
    (hact : F.canonicalAge.PartialSpanActual S) :
    ∃ g, F.canonicalAge.PartialRealizesAt (H.capRight S) S.right.codIdx
        (encode (H.capApex S)) g ∧ H.PrefixBehavior S g :=
  ⟨_, (H.exists_closingRealizer hact).choose_spec.1,
    (H.exists_closingRealizer hact).choose_spec.2⟩

/-- The square, and the right leg's actualness — the two consequences of the halves above. -/
theorem test_soundness {S : PotentialSpanData}
    (hact : F.canonicalAge.PartialSpanActual S) :
    F.canonicalAge.PartialIsEmbedding (H.capSelect S).rightToApex ∧
      F.canonicalAge.PartialCommutes S (H.capSelect S) :=
  ⟨H.capRight_isEmbedding_of_actual hact, H.capSelect_commutes hact⟩

/-! ### The empty-generator boundary -/

/-- **A right member with no recorded generators.** The fold does nothing: no chosen images, and the
apex is the left member's generators unchanged. -/
theorem test_empty_right_generators {S : PotentialSpanData}
    (h : allTupleFor S.right.codIdx = []) :
    H.capChosen S = [] ∧ H.capApex S = allTupleFor S.left.codIdx := by
  have hlen : (H.capChosen S).length = 0 := by rw [H.capChosen_length, h]; rfl
  have hnil : H.capChosen S = [] := List.eq_nil_of_length_eq_zero hlen
  exact ⟨hnil, by rw [ComputablyHomogeneousIn.capApex, hnil, List.append_nil]⟩

/-! ### The theorem -/

include H

/-- **CAP for the canonical age**, from computable homogeneity alone. `E` unrelated to `O`. -/
theorem test_canonical_cap : F.canonicalAge.PartialCAPIn E :=
  ComputablyHomogeneousIn.canonicalAge_partialCAPIn_of_computablyHomogeneous H

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.test_selector_total_and_effective
#assert_standard_axioms FirstOrder.Language.test_chain_computable
#assert_standard_axioms FirstOrder.Language.test_malformed_unconditional
#assert_standard_axioms FirstOrder.Language.test_apex_shape
#assert_standard_axioms FirstOrder.Language.test_offset_behaviour
#assert_standard_axioms FirstOrder.Language.test_prefix_behaviour
#assert_standard_axioms FirstOrder.Language.test_soundness
#assert_standard_axioms FirstOrder.Language.test_empty_right_generators
#assert_standard_axioms FirstOrder.Language.test_canonical_cap
