/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.BackForthRun
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: the stage recursion

Four obligations.

**One round is both halves at one stage.** `test_round_is_both_halves_at_one_stage` reads the round
back as the literal composite, with the *same* `n` passed to each half, and then reads off what each
half contributed: `n` lands on the source side, and `n` again on the target side. A parity scheme
would fail the first conjunct by shape and the second numerically.

**The two discovery positions differ.** `test_discovery_positions` puts the source occurrence of `n`
at `2 * n` and the target occurrence at `2 * n + 1`, and records that these are different positions.
The asymmetry is not incidental: the source tuple's `2 * n + 1` entry is whatever the back half's
homogeneity chose, and the target tuple's `2 * n` entry is whatever the forth half's chose. Reading
either occurrence at the other's position would be wrong, and this row is what would catch it.

**The invariant holds throughout**, at every stage and not merely in the limit —
`test_invariant_throughout`, by the induction in `stateAt_matched`.

**The whole run is computable at `E`**, with `O` unrelated — `test_run_computable_no_inclusion`.
The binders carry the point: two covers and two homogeneity selectors at an arbitrary `E`, two
structures presented at `O`, and no hypothesis relating them.

Persistence is gated alongside, since it is what the next unit consumes: prefix at a successor, and
at an arbitrary `m ≤ n`.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

section Run

variable {E : Set (ℕ →. ℕ)} {S T : ComputableStructureIn O L}
  (r : RepresentationCoverIn E S.canonicalAge T.canonicalAge)
  (rb : RepresentationCoverIn E T.canonicalAge S.canonicalAge)
  (H : ComputablyHomogeneousIn E T) (Hs : ComputablyHomogeneousIn E S)

/-- **One round performs both halves at the same stage.** The first conjunct is the composite by
shape — `n` is passed to the forth half and the *same* `n` to the back half, which runs on the state
the forth half produced. The next two say what each half put where. -/
theorem test_round_is_both_halves_at_one_stage (n : ℕ) (s : BackForthState) :
    BackForthState.roundState r rb H Hs n s
        = BackForthState.backState rb (BackForthState.forthState r s n H) n Hs ∧
      (BackForthState.roundState r rb H Hs n s).sourceTuple
          = s.sourceTuple ++ [n, BackForthState.roundBackPoint r rb H Hs n s] ∧
        (BackForthState.roundState r rb H Hs n s).targetTuple
          = s.targetTuple ++ [BackForthState.roundForthPoint r H n s, n] :=
  ⟨rfl, BackForthState.roundState_sourceTuple r rb H Hs n s,
    BackForthState.roundState_targetTuple r rb H Hs n s⟩

/-- The round preserves the invariant, which is what makes the recursion legitimate. -/
theorem test_round_preserves_matched (n : ℕ) {s : BackForthState} (h : s.Matched S T) :
    (BackForthState.roundState r rb H Hs n s).Matched S T :=
  BackForthState.roundState_matched r rb H Hs n h

/-- The run's two equations, and its lengths: both tuples grow by exactly two per round. -/
theorem test_run_equations_and_lengths (n : ℕ) :
    BackForthState.stateAt r rb H Hs 0 = BackForthState.empty ∧
      BackForthState.stateAt r rb H Hs (n + 1)
          = BackForthState.roundState r rb H Hs n (BackForthState.stateAt r rb H Hs n) ∧
        (BackForthState.stateAt r rb H Hs n).sourceTuple.length = 2 * n ∧
          (BackForthState.stateAt r rb H Hs n).targetTuple.length = 2 * n :=
  ⟨rfl, rfl, BackForthState.stateAt_sourceTuple_length r rb H Hs n,
    BackForthState.stateAt_targetTuple_length r rb H Hs n⟩

/-- **The two discovery positions, and that they differ.** `n` is at source position `2 * n` and at
target position `2 * n + 1`. -/
theorem test_discovery_positions (n : ℕ) :
    (BackForthState.stateAt r rb H Hs (n + 1)).sourceTuple[2 * n]? = some n ∧
      (BackForthState.stateAt r rb H Hs (n + 1)).targetTuple[2 * n + 1]? = some n ∧
        2 * n ≠ 2 * n + 1 :=
  ⟨BackForthState.stateAt_sourceTuple_getElem?_two_mul r rb H Hs n,
    BackForthState.stateAt_targetTuple_getElem?_two_mul_succ r rb H Hs n, by omega⟩

/-- **The invariant holds at every stage**, not only in the limit. -/
theorem test_invariant_throughout (n : ℕ) : (BackForthState.stateAt r rb H Hs n).Matched S T :=
  BackForthState.stateAt_matched r rb H Hs n

/-- **The whole run is computable in the map oracle**, with `E` unrelated to `O`: no inclusion
appears in the binders, and none is used. -/
theorem test_run_computable_no_inclusion :
    ComputableIn E (BackForthState.stateAt r rb H Hs) ∧
      ComputableIn E fun p : ℕ × BackForthState ↦ BackForthState.roundState r rb H Hs p.1 p.2 :=
  ⟨BackForthState.stateAt_computableIn r rb H Hs,
    BackForthState.roundState_computableIn r rb H Hs⟩

/-- **Persistence**, at a successor and at an arbitrary pair of stages. Nothing is ever revised, so
a value read at one stage is readable at the same position at every later one — the input the total
maps will need. -/
theorem test_persistence {m n : ℕ} (h : m ≤ n) :
    (BackForthState.stateAt r rb H Hs m).sourceTuple
        <+: (BackForthState.stateAt r rb H Hs n).sourceTuple ∧
      (BackForthState.stateAt r rb H Hs m).targetTuple
          <+: (BackForthState.stateAt r rb H Hs n).targetTuple ∧
        (BackForthState.stateAt r rb H Hs m).sourceTuple
          <+: (BackForthState.stateAt r rb H Hs (m + 1)).sourceTuple :=
  ⟨BackForthState.stateAt_sourceTuple_prefix r rb H Hs h,
    BackForthState.stateAt_targetTuple_prefix r rb H Hs h,
    BackForthState.stateAt_sourceTuple_prefix_succ r rb H Hs m⟩

end Run

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.test_round_is_both_halves_at_one_stage
#assert_standard_axioms FirstOrder.Language.test_round_preserves_matched
#assert_standard_axioms FirstOrder.Language.test_run_equations_and_lengths
#assert_standard_axioms FirstOrder.Language.test_discovery_positions
#assert_standard_axioms FirstOrder.Language.test_invariant_throughout
#assert_standard_axioms FirstOrder.Language.test_run_computable_no_inclusion
#assert_standard_axioms FirstOrder.Language.test_persistence
