/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.AgeChainSchedule
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: the CJEP schedule

The live error here is not arithmetic, it is **which leg does which job**. The schedule feeds the
previous stage on the left and the next original index on the right, so:

* the left leg runs `d n → d (n+1)` and is the chain step;
* the right leg runs `n → d (n+1)` and is what makes the schedule cofinal.

Swapping them would still typecheck — both are potential embedding data into the same apex — and
would silently produce a chain that is either cofinal by accident or not at all. The index rows
below pin each leg's *source*, which is exactly where the two differ.

No fixture is needed: these are statements about the schedule itself, and stating them over an
arbitrary family is stronger than exhibiting one.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

namespace PartialAgeIn

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable (sel : ℕ → ℕ → PartialJointEmbeddingData) (baseIdx : ℕ)

/-- The schedule starts at the **named** base index, not at `0`. -/
theorem test_schedule_starts_at_base : cjepSchedule sel baseIdx 0 = baseIdx := rfl

/-- And steps by joint-embedding the previous stage with the next original index — in that order. -/
theorem test_schedule_succ (n : ℕ) :
    cjepSchedule sel baseIdx (n + 1) = (sel (cjepSchedule sel baseIdx n) n).apexIdx := rfl

/-- **The chain step runs out of the previous stage.** -/
theorem test_step_leg_source (n : ℕ) :
    (stepData sel baseIdx n).domIdx = cjepSchedule sel baseIdx n ∧
      (stepData sel baseIdx n).codIdx = cjepSchedule sel baseIdx (n + 1) :=
  ⟨rfl, rfl⟩

/-- **The cofinality leg runs out of the original member `n`** — not out of the schedule. This is
the row that separates the two legs. -/
theorem test_cofinal_leg_source (n : ℕ) :
    (cofinalData sel baseIdx n).domIdx = n ∧
      (cofinalData sel baseIdx n).codIdx = cjepSchedule sel baseIdx (n + 1) :=
  ⟨rfl, rfl⟩

/-- Every original index is scheduled: member `n` lands in stage `n + 1`, so the schedule is cofinal
in the representation rather than merely infinite. -/
theorem test_schedule_cofinal {K : PartialAgeIn O L} (hspec : K.JointSpec sel) (n : ℕ) :
    K.PartialIsEmbedding (cofinalData sel baseIdx n) ∧
      (cofinalData sel baseIdx n).domIdx = n :=
  ⟨cofinalData_partialIsEmbedding hspec n, rfl⟩

/-- **Nonemptiness reaches every stage from the single base witness** — and is available before any
enumeration is totalized, which is what keeps `firstSomeStep` non-circular. -/
theorem test_nonempty_propagates {K : PartialAgeIn O L} (hspec : K.JointSpec sel)
    (hbase : (K.domainAt baseIdx).Nonempty) (n : ℕ) :
    (K.domainAt (cjepSchedule sel baseIdx n)).Nonempty :=
  cjepSchedule_domainAt_nonempty hspec hbase n

/-- The two extractions of the previous file are therefore available along the schedule. -/
theorem test_witness_available {K : PartialAgeIn O L} (hspec : K.JointSpec sel)
    (hbase : (K.domainAt baseIdx).Nonempty) (n : ℕ) :
    K.firstEnumeratedValue (cjepSchedule sel baseIdx)
        (cjepSchedule_domainAt_nonempty hspec hbase) n ∈
      K.domainAt (cjepSchedule sel baseIdx n) :=
  K.firstEnumeratedValue_mem _ _ n

end PartialAgeIn

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_schedule_starts_at_base
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_schedule_succ
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_step_leg_source
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_cofinal_leg_source
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_schedule_cofinal
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_nonempty_propagates
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_witness_available
