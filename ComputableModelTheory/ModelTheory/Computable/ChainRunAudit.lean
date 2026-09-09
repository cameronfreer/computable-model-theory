/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.ChainRun
import ComputableModelTheory.ModelTheory.Computable.CollapsingCandidate
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: the run and scheduler agreement

**The run.** `test_recurrence` is the exact recurrence; `test_halting_and_invariant` gates halting
and the invariant at every stage with no actualness or fairness hypothesis; `test_links` are the
two membership links (`run_mem`, `run_succ_mem`) through which the transition's specification is
consumed without unfolding `.get`; `test_effective` is the totalized run's computability, the only
row with `O ⊆ E`.

**Scheduler agreement.** `test_persistence` (prefixes are never revised), `test_history_agrees`
(the run's history represents `memberIdx` at every earlier stage), and `test_fired_agrees` — the
bridge: the run's fired record is the scheduler's. `test_firing_iff` reads firing off the run's own
fired record.

**Fairness and one-shot, transferred.** `test_admissible_fires` and `test_fires_once` are the
scheduler theorems certifying the actual construction, through the agreement rather than by reproof.

**The deferred audit row.** `test_collapsing_code_fires` closes the boundary left open in the
transition audit (fixture shared through `CollapsingCandidate`): the collapsing candidate is
admissible for the constructed chain (its static guards hold, and the lifted family has full
carriers), so its encoding **does** fire at some stage of the run, at which the transition selects
that code, decodes it back to the candidate, and extends
the chain by a CAP output — while the candidate's chain map is not an embedding. This is the full
scheduling path, from coverage through fairness to the firing step.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

section General

variable {K : PartialAgeIn O L} (W : PartialCAPWitness E K) (i : ℕ)

/-- **The exact recurrence.** -/
theorem test_recurrence (s : ℕ) :
    PartialAgeIn.runPart K W i (s + 1) =
      (PartialAgeIn.runPart K W i s).bind fun S ↦ PartialAgeIn.stepPart K W S s :=
  PartialAgeIn.runPart_succ K W i s

/-- **Halting and the invariant at every stage**, with no actualness or fairness hypothesis. -/
theorem test_halting_and_invariant (s : ℕ) :
    (PartialAgeIn.runPart K W i s).Dom ∧ K.RunInvariant (PartialAgeIn.run K W i s) s :=
  ⟨PartialAgeIn.runPart_dom s, PartialAgeIn.run_runInvariant s⟩

/-- **The two links.** -/
theorem test_links (s : ℕ) :
    PartialAgeIn.run K W i s ∈ PartialAgeIn.runPart K W i s ∧
      PartialAgeIn.run K W i (s + 1) ∈ PartialAgeIn.stepPart K W (PartialAgeIn.run K W i s) s :=
  ⟨PartialAgeIn.run_mem s, PartialAgeIn.run_succ_mem s⟩

/-- **Effectivity of the totalized run** — the only row with `O ⊆ E`. -/
theorem test_effective (hOE : O ⊆ E) : ComputableIn E (PartialAgeIn.run K W i) :=
  PartialAgeIn.run_computableIn hOE

/-- **Persistence.** -/
theorem test_persistence {s t : ℕ} (h : s ≤ t) :
    (PartialAgeIn.run K W i s).stages <+: (PartialAgeIn.run K W i t).stages :=
  PartialAgeIn.run_stages_prefix h

/-- **History agreement** at every earlier stage. -/
theorem test_history_agrees (s : ℕ) : ∀ r ≤ s,
    (stageHistory (PartialAgeIn.run K W i s).stages)[r]? = some (PartialAgeIn.memberIdx K W i r) :=
  PartialAgeIn.history_agrees s

/-- **The bridge**: the run's fired record is the scheduler's. -/
theorem test_fired_agrees (s : ℕ) :
    (PartialAgeIn.run K W i s).fired = (PartialAgeIn.schedule K W i).fired s :=
  PartialAgeIn.run_fired_eq s

/-- **Firing, read off the run.** -/
theorem test_firing_iff (e s : ℕ) :
    (PartialAgeIn.schedule K W i).FiresAt e s ↔
      (PartialAgeIn.run K W i (s + 1)).fired = (PartialAgeIn.run K W i s).fired ++ [e] :=
  PartialAgeIn.firesAt_iff_fired

/-- **Fairness, transferred.** -/
theorem test_admissible_fires {q : RequirementData}
    (hq : K.Admissible (PartialAgeIn.memberIdx K W i) q) :
    ∃ s, (PartialAgeIn.schedule K W i).FiresAt (encode q) s :=
  PartialAgeIn.exists_firesAt_of_admissible hq

/-- **One-shot, transferred.** -/
theorem test_fires_once {e s t : ℕ} (hs : (PartialAgeIn.schedule K W i).FiresAt e s)
    (ht : (PartialAgeIn.schedule K W i).FiresAt e t) : s = t :=
  PartialAgeIn.firesAt_unique hs ht

end General

/-! ### The deferred row: the collapsing candidate's code fires in the constructed run -/

section Fixture

variable (O : Set (ℕ →. ℕ))

/-- **The full scheduling path.** The collapsing candidate is admissible for the constructed chain,
so its encoding fires at some stage; at that stage the run's transition selects it, decodes it back
to the candidate, extends the chain by a CAP output, and appends the code — while the candidate's
chain map is not an embedding. -/
theorem test_collapsing_code_fires (W : PartialCAPWitness E (threeWidthFamily O)) (i : ℕ) :
    ∃ s, (PartialAgeIn.schedule (threeWidthFamily O) W i).FiresAt (encode collapsingCandidate) s ∧
      (∃ D : AmalgamationDiagramData,
        PartialAgeIn.run (threeWidthFamily O) W i (s + 1) =
          (PartialAgeIn.run (threeWidthFamily O) W i s).capExtension
            (encode collapsingCandidate) D) ∧
      (PartialAgeIn.run (threeWidthFamily O) W i (s + 1)).fired =
        (PartialAgeIn.run (threeWidthFamily O) W i s).fired ++ [encode collapsingCandidate] ∧
      ¬ (threeWidthFamily O).PartialIsEmbedding
        (collapsingCandidate.chainMap (PartialAgeIn.run (threeWidthFamily O) W i s).dHist) := by
  have hadm : (threeWidthFamily O).Admissible (PartialAgeIn.memberIdx (threeWidthFamily O) W i)
      collapsingCandidate :=
    ⟨collapsingCandidate_staticAdmissible O,
      (collapsingCandidate_carrierValid O (PartialAgeIn.memberIdx (threeWidthFamily O) W i)).1,
      (collapsingCandidate_carrierValid O (PartialAgeIn.memberIdx (threeWidthFamily O) W i)).2⟩
  obtain ⟨s, hs⟩ := PartialAgeIn.exists_firesAt_of_admissible hadm
  obtain ⟨q, hq, -, -, -, -, D, -, hrun⟩ := PartialAgeIn.exists_capExtension_of_firesAt hs
  rw [RequirementData.decode_encode] at hq
  obtain rfl := Option.some.inj hq
  exact ⟨s, hs, ⟨D, hrun⟩, PartialAgeIn.firesAt_iff_fired.1 hs,
    collapsingCandidate_not_partialIsEmbedding O _⟩

end Fixture

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.test_recurrence
#assert_standard_axioms FirstOrder.Language.test_halting_and_invariant
#assert_standard_axioms FirstOrder.Language.test_links
#assert_standard_axioms FirstOrder.Language.test_effective
#assert_standard_axioms FirstOrder.Language.test_persistence
#assert_standard_axioms FirstOrder.Language.test_history_agrees
#assert_standard_axioms FirstOrder.Language.test_fired_agrees
#assert_standard_axioms FirstOrder.Language.test_firing_iff
#assert_standard_axioms FirstOrder.Language.test_admissible_fires
#assert_standard_axioms FirstOrder.Language.test_fires_once
#assert_standard_axioms FirstOrder.Language.test_collapsing_code_fires
