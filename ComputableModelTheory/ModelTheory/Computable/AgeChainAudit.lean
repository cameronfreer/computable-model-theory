/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.AgeChain
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: the c.e. structure chain of a CJEP schedule

The headline row is `test_chain_from_cjep`: the joint embedding property and a **single named base
witness** are between them enough to produce a c.e. structure chain. Everything the construction
needs beyond that — nonemptiness at every stage, total stage enumerations, uniformly partial
recursive steps — is derived rather than assumed, so the row is a statement about how little input
is required.

The remaining rows pin the two boundary facts the assembly rests on: that totalizing the stages did
not move their carriers, and that the chain's steps are the left legs and nothing else. Both are the
places where a plausible-looking construction could silently drift from the scheduled members it is
supposed to present.

The oracle split stays visible in the statement: the family is computable in the presentation
oracle `O`, the selector in the map oracle `E`, and the chain lives at `E` under `O ⊆ E`.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

namespace PartialAgeIn

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-- **CJEP and a base witness give a c.e. structure chain.** No certificate, no decidability, and no
hypothesis about members off the schedule. -/
theorem test_chain_from_cjep {K : PartialAgeIn O L} (h : K.PartialCJEPIn E) (hOE : O ⊆ E)
    (baseIdx : ℕ) (hbase : (K.domainAt baseIdx).Nonempty) :
    Nonempty (CeStructureChainIn E L) := by
  obtain ⟨sel, hsel, hspec⟩ := PartialCJEPIn.exists_jointSpec h
  exact ⟨cjepChain K sel baseIdx (cjepSchedule_domainAt_nonempty hspec hbase) hOE hspec hsel⟩

variable (K : PartialAgeIn O L) (sel : ℕ → ℕ → PartialJointEmbeddingData) (baseIdx : ℕ)
  (hne : ∀ n, (K.domainAt (cjepSchedule sel baseIdx n)).Nonempty) (hOE : O ⊆ E)

/-- **Totalizing did not move the carriers.** The stage carriers are exactly the scheduled members'
carriers — the fact every step law is rewritten through, and the one a fallback-based totalization
could plausibly break. -/
theorem test_chain_stage_domain (hspec : K.JointSpec sel)
    (hsel : ComputableIn E fun p : ℕ × ℕ ↦ sel p.1 p.2) (n : ℕ) :
    ((cjepChain K sel baseIdx hne hOE hspec hsel).stageAt n).domain =
      K.domainAt (cjepSchedule sel baseIdx n) :=
  cjepChain_stage_domain K sel baseIdx hne hOE hspec hsel n

/-- The stage enumeration falls back to the extracted witness, and to nothing else. -/
theorem test_chain_stage_enum (hspec : K.JointSpec sel)
    (hsel : ComputableIn E fun p : ℕ × ℕ ↦ sel p.1 p.2) (n m : ℕ) :
    ((cjepChain K sel baseIdx hne hOE hspec hsel).stageAt n).enum m =
      (K.enum? (cjepSchedule sel baseIdx n) m).getD
        (K.firstEnumeratedValue (cjepSchedule sel baseIdx) hne n) :=
  scheduledStage_enum (hOE := hOE) n m

/-- **The chain's steps are the left legs.** Not the cofinality legs, and not a totalization of
either: `chainStep` is `applyPotentialPart` on `stepData`, which runs `d n → d (n+1)`. -/
theorem test_chain_step_is_left_leg (hspec : K.JointSpec sel)
    (hsel : ComputableIn E fun p : ℕ × ℕ ↦ sel p.1 p.2) (n x : ℕ) :
    (cjepChain K sel baseIdx hne hOE hspec hsel).step n x =
      K.applyPotentialPart (stepData sel baseIdx n) x :=
  rfl

/-- And the left leg's endpoints are the two consecutive stages, on the nose. -/
theorem test_chain_step_endpoints (n : ℕ) :
    (stepData sel baseIdx n).domIdx = cjepSchedule sel baseIdx n ∧
      (stepData sel baseIdx n).codIdx = cjepSchedule sel baseIdx (n + 1) :=
  ⟨rfl, rfl⟩

end PartialAgeIn

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_chain_from_cjep
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_chain_stage_domain
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_chain_stage_enum
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_chain_step_is_left_leg
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_chain_step_endpoints
