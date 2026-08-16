/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.AgeChainSteps
import ComputableModelTheory.ModelTheory.Computable.CeStructureChain

/-!
# The c.e. structure chain of a CJEP schedule

The assembly. Totality enters here and only here: the *stage presentations* are totalized, by
`toCePresentation` at the uniformly extracted witnesses, while the embeddings between them stay
partial. That split is the whole shape of the construction —

* partiality belongs to the embeddings (`chainStep`, `Part`-valued as `CeStructureChainIn.step` is);
* totality belongs to the stage enumerations, and is bought by the base witness.

Exactly two facts cross the boundary between a scheduled member and its totalized stage:
`scheduledStage_domain`, which says totalizing did not move the carrier, and `scheduledStage_enum`,
which names the totalized enumeration. The first is what the four step laws are rewritten through;
the second is what makes `enum_uniform` a direct composition, with no per-stage computability
entering it — per-stage facts never imply uniform ones, which is the trap this layer exists to
avoid.

The rewrites stay at the outer boundary, and `CeStructureChainIn` states everything over raw
naturals rather than carrier subtypes, so no dependent motive is involved.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

namespace PartialAgeIn

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable (K : PartialAgeIn O L) (sel : ℕ → ℕ → PartialJointEmbeddingData) (baseIdx : ℕ)
  (hne : ∀ n, (K.domainAt (cjepSchedule sel baseIdx n)).Nonempty) (hOE : O ⊆ E)

/-! ### The totalized stages -/

include hne hOE in
/-- The `n`-th stage: the scheduled member, totalized at its uniformly extracted witness, and lifted
to the map oracle. -/
noncomputable def scheduledStage (n : ℕ) : CePresentationIn E L :=
  ((K.memberAt (cjepSchedule sel baseIdx n)).toCePresentation
    (K.enum?_firstSomeStep (cjepSchedule sel baseIdx) hne n)).mono hOE

variable {K sel baseIdx hne hOE}

/-- **Totalizing did not move the carrier.** The one fact the step laws are rewritten through. -/
theorem scheduledStage_domain (n : ℕ) :
    (scheduledStage K sel baseIdx hne hOE n).domain =
      K.domainAt (cjepSchedule sel baseIdx n) :=
  (K.memberAt (cjepSchedule sel baseIdx n)).toCePresentation_domain
    (K.enum?_firstSomeStep (cjepSchedule sel baseIdx) hne n)

/-- **The totalized enumeration, named.** Silent steps fall back to the extracted witness. -/
theorem scheduledStage_enum (n m : ℕ) :
    (scheduledStage K sel baseIdx hne hOE n).enum m =
      (K.enum? (cjepSchedule sel baseIdx n) m).getD
        (K.firstEnumeratedValue (cjepSchedule sel baseIdx) hne n) :=
  rfl

/-- Uniform computability of the stage enumerations — a direct composition of the family's uniformly
computable partial enumeration with the extracted witnesses. No per-stage computability enters:
per-stage facts do not imply uniform ones. -/
theorem scheduledStage_enum_uniform
    (hsel : ComputableIn E fun p : ℕ × ℕ ↦ sel p.1 p.2) :
    ComputableIn E fun p : ℕ × ℕ ↦ (scheduledStage K sel baseIdx hne hOE p.1).enum p.2 := by
  have hd : ComputableIn E (cjepSchedule sel baseIdx) := cjepSchedule_computableIn sel baseIdx hsel
  have henum : ComputableIn E fun p : ℕ × ℕ ↦ K.enum? (cjepSchedule sel baseIdx p.1) p.2 :=
    (RecursiveIn.mono hOE K.enum?_computableIn).comp
      ((hd.comp ComputableIn.fst).pair ComputableIn.snd)
  have hwit : ComputableIn E fun p : ℕ × ℕ ↦
      K.firstEnumeratedValue (cjepSchedule sel baseIdx) hne p.1 :=
    (K.firstEnumeratedValue_computableIn (cjepSchedule sel baseIdx) hne hOE hd).comp
      ComputableIn.fst
  exact (ComputableIn.option_casesOn henum hwit ComputableIn.snd.to₂).of_eq fun p ↦ by
    rw [scheduledStage_enum]
    cases K.enum? (cjepSchedule sel baseIdx p.1) p.2 <;> rfl

/-! ### The chain -/

variable (K sel baseIdx hne hOE)

include hne hOE in
/-- **The c.e. structure chain of a CJEP schedule.** Stages are the totalized scheduled members;
steps are the left legs, still partial. The chain lives at the map oracle `E`, since that is where
the selector lives, and `O ⊆ E` is what lets the family's data meet it. -/
noncomputable def cjepChain (hspec : K.JointSpec sel)
    (hsel : ComputableIn E fun p : ℕ × ℕ ↦ sel p.1 p.2) : CeStructureChainIn E L where
  stageAt := scheduledStage K sel baseIdx hne hOE
  enum_uniform := scheduledStage_enum_uniform hsel
  step := chainStep K sel baseIdx
  step_recursiveIn :=
    RecursiveIn.comp (O := E) (α := ℕ × ℕ) (β := PotentialEmbeddingData × ℕ) (σ := ℕ)
      (f := fun q : PotentialEmbeddingData × ℕ ↦ K.applyPotentialPart q.1 q.2)
      (g := fun p : ℕ × ℕ ↦ (stepData sel baseIdx p.1, p.2))
      (RecursiveIn.mono hOE K.applyPotentialPart_recursiveIn)
      (((stepData_computableIn hsel).comp ComputableIn.fst).pair ComputableIn.snd)
  step_mem := fun i x hx ↦ by
    rw [scheduledStage_domain] at hx
    simpa only [scheduledStage_domain] using chainStep_mem hspec i x hx
  step_injOn := fun i x₁ x₂ y hx₁ hx₂ h₁ h₂ ↦ by
    rw [scheduledStage_domain] at hx₁ hx₂
    exact chainStep_injOn hspec i x₁ x₂ y hx₁ hx₂ h₁ h₂
  step_funMap := fun i n f v w hv hw ↦ by
    simp only [scheduledStage_domain] at hv
    exact chainStep_funMap hspec i n f v w hv hw
  step_relMap := fun i n R v w hv hw ↦ by
    simp only [scheduledStage_domain] at hv
    exact chainStep_relMap hspec i n R v w hv hw

@[simp] theorem cjepChain_stageAt (hspec : K.JointSpec sel)
    (hsel : ComputableIn E fun p : ℕ × ℕ ↦ sel p.1 p.2) (n : ℕ) :
    (cjepChain K sel baseIdx hne hOE hspec hsel).stageAt n =
      scheduledStage K sel baseIdx hne hOE n :=
  rfl

@[simp] theorem cjepChain_step (hspec : K.JointSpec sel)
    (hsel : ComputableIn E fun p : ℕ × ℕ ↦ sel p.1 p.2) :
    (cjepChain K sel baseIdx hne hOE hspec hsel).step = chainStep K sel baseIdx :=
  rfl

/-- The chain's stage carriers are the scheduled members' carriers, unchanged. -/
theorem cjepChain_stage_domain (hspec : K.JointSpec sel)
    (hsel : ComputableIn E fun p : ℕ × ℕ ↦ sel p.1 p.2) (n : ℕ) :
    ((cjepChain K sel baseIdx hne hOE hspec hsel).stageAt n).domain =
      K.domainAt (cjepSchedule sel baseIdx n) :=
  scheduledStage_domain (hOE := hOE) n

include hne hOE in
/-- **The chain's stage evaluators are uniformly partial recursive.** Certificate-independent, and
a direct composition: the stage evaluators *are* the family's, read at the scheduled index. This is
explicit input data for every limit construction, since per-stage recursiveness never implies
uniformity. -/
theorem cjepChain_uniformEvaluators (hspec : K.JointSpec sel)
    (hsel : ComputableIn E fun p : ℕ × ℕ ↦ sel p.1 p.2) :
    (cjepChain K sel baseIdx hne hOE hspec hsel).UniformEvaluatorsIn where
  funEval_uniform := by
    have hd : ComputableIn E (cjepSchedule sel baseIdx) := cjepSchedule_computableIn sel baseIdx hsel
    exact ((RecursiveIn.mono hOE K.funEval_recursiveIn).comp
      ((hd.comp ComputableIn.fst).pair ComputableIn.snd)).of_eq fun _ ↦ rfl
  relEval_uniform := by
    have hd : ComputableIn E (cjepSchedule sel baseIdx) := cjepSchedule_computableIn sel baseIdx hsel
    exact ((RecursiveIn.mono hOE K.relEval_recursiveIn).comp
      ((hd.comp ComputableIn.fst).pair ComputableIn.snd)).of_eq fun _ ↦ rfl

end PartialAgeIn

end FirstOrder.Language
