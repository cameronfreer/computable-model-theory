/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.ChainHistory
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: the recorded finite chain

**Two composition contracts, gated separately.** `test_compPart_carrierValid` is the one the firing
step consumes: matching middle indices, a *carrier-valid* candidate, an *actual* transport — and the
composite halts, has the outer endpoints, and is carrier-valid. `test_compPart_realizer` is the one
the commuting square consumes: both maps actual, the realizer named as `g.comp f`.
`test_compPart_exists` is the latter's existential shadow.

**The fixture that tells them apart.** `nonactualCandidate` is `A_1 → A_0` with range `[7]`: carrier
valid (the lifted family has full carriers) but **not** an embedding, since `A_1` has two recorded
generators and the range has one entry. `test_nonactual_candidate_composes` proves nonactualness
*alongside* convergence and landing of its composite with the identity. Using the stronger
composition theorem at the firing step would reject exactly this candidate — and silently restrict
which requirements the construction processes, with nothing complaining.

**Transport obeys its two laws and lands where it should.** `test_transport_self` and
`test_transport_succ` are the laws the recursion will unfold; `test_transport_lands` says that under
the invariant the fold halts on an actual embedding from the member recorded at `r` to the member
recorded at `s`. No `CeStructureChainIn` appears anywhere in this audit.

**The invariant extends by one stage.** `test_invariant_base` and `test_invariant_snoc` are the only
two facts about `ChainInvariant` the recursion will use; nothing else is asserted about it here.

**Selection agrees with the scheduler.** `test_pick_agrees` says selection from a representing
history is the scheduler's selection at `d`. This is the link scheduler agreement will run along.

**Effectivity with no member-index hypothesis.** `test_effective` records that composition and
transport are partial recursive, and selection computable, at any oracle reading the family — with
nothing assumed about any `d`.

**A concrete two-stage chain.** On the lifted two-width successor family, a base stage on member
`0` extended by the identity data into member `0` again satisfies the invariant, and transport from
`0` to `1` halts on data whose endpoints are both `0`. The identity step is exactly the *silent*
step of the clock-stage recursion, so this is the fixture that step will be measured against.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

section General

variable (K : PartialAgeIn O L)

/-- **The composite's realizer**, named: `g.comp f`, with the composite range tuple exhibited. -/
theorem test_compPart_realizer {c d e : ℕ} {w v : Tuple ℕ}
    {f : (K.memberAt c).domain ↪[L] (K.memberAt d).domain}
    {g : (K.memberAt d).domain ↪[L] (K.memberAt e).domain}
    (hf : K.PartialRealizes (PotentialEmbeddingData.ofTriple (c, d, w)) f)
    (hg : K.PartialRealizes (PotentialEmbeddingData.ofTriple (d, e, v)) g) :
    ∃ v' : Tuple ℕ,
      K.compPart (PotentialEmbeddingData.ofTriple (d, e, v))
          (PotentialEmbeddingData.ofTriple (c, d, w)) =
        Part.some (PotentialEmbeddingData.ofTriple (c, e, v')) ∧
      K.PartialRealizes (PotentialEmbeddingData.ofTriple (c, e, v')) (g.comp f) :=
  K.compPart_realizes hf hg

/-- **The firing-step contract**: carrier validity of the candidate, actualness of the transport,
matching middle indices — and nothing about the candidate's width or actualness. -/
theorem test_compPart_carrierValid {G F : PotentialEmbeddingData} (hFG : F.codIdx = G.domIdx)
    (hF : K.CarrierValid F) (hG : K.PartialIsEmbedding G) :
    ∃ H ∈ K.compPart G F, H.domIdx = F.domIdx ∧ H.codIdx = G.codIdx ∧ K.CarrierValid H :=
  K.compPart_carrierValid hFG hF hG

/-- **The existential shadow**, on arbitrary data with matching middle member. -/
theorem test_compPart_exists {G F : PotentialEmbeddingData} (hFG : F.codIdx = G.domIdx)
    (hF : K.PartialIsEmbedding F) (hG : K.PartialIsEmbedding G) :
    ∃ H ∈ K.compPart G F, H.domIdx = F.domIdx ∧ H.codIdx = G.codIdx ∧ K.PartialIsEmbedding H :=
  K.compPart_partialIsEmbedding hFG hF hG

/-- **Transport law, base.** -/
theorem test_transport_self (stages : List StageRecord) (r : ℕ) :
    K.transportPart stages r r = Part.some (K.idData ((stageHistory stages).getD r 0)) :=
  K.transportPart_self stages r

/-- **Transport law, step.** -/
theorem test_transport_succ (stages : List StageRecord) {r s : ℕ} (hrs : r ≤ s)
    {rec : StageRecord} (hrec : stages[s + 1]? = some rec) :
    K.transportPart stages r (s + 1) =
      (K.transportPart stages r s).bind fun H ↦ K.compPart rec.step H :=
  K.transportPart_succ stages hrs hrec

/-- **Transport lands**: under the invariant, on an actual embedding between the recorded
members. -/
theorem test_transport_lands {stages : List StageRecord} (h : K.ChainInvariant stages) {r s : ℕ}
    (hrs : r ≤ s) {rr rs : StageRecord} (hr : stages[r]? = some rr) (hs : stages[s]? = some rs) :
    ∃ H ∈ K.transportPart stages r s,
      H.domIdx = rr.memberIdx ∧ H.codIdx = rs.memberIdx ∧ K.PartialIsEmbedding H :=
  K.transportPart_partialIsEmbedding h hrs hr hs

/-- **Invariant, base.** -/
theorem test_invariant_base (i : ℕ) : K.ChainInvariant [⟨i, K.idData i⟩] :=
  K.chainInvariant_base i

/-- **Invariant, extension by one actual step out of the last recorded member.** -/
theorem test_invariant_snoc {stages : List StageRecord} (h : K.ChainInvariant stages) {j : ℕ}
    {F : PotentialEmbeddingData} (hdom : ∀ r ∈ stages.getLast?, F.domIdx = r.memberIdx)
    (hcod : F.codIdx = j) (hF : K.PartialIsEmbedding F) :
    K.ChainInvariant (stages ++ [⟨j, F⟩]) :=
  h.snoc hdom hcod hF

/-- **Selection agrees with the scheduler** on a representing history. -/
theorem test_pick_agrees {d : ℕ → ℕ} {hist : List ℕ} {s : ℕ}
    (hh : ∀ r ≤ s, hist[r]? = some (d r)) (fired : List ℕ) :
    K.pickFromHistory hist fired s = (K.requirementDovetail d).pick fired s :=
  K.pickFromHistory_eq hh fired

/-- **Effectivity with no member-index hypothesis.** -/
theorem test_effective (hOE : O ⊆ E) :
    RecursiveIn E (fun p : PotentialEmbeddingData × PotentialEmbeddingData ↦ K.compPart p.1 p.2) ∧
      RecursiveIn E (fun p : (List StageRecord × ℕ) × ℕ ↦ K.transportPart p.1.1 p.1.2 p.2) ∧
        ComputableIn E (fun p : (List ℕ × List ℕ) × ℕ ↦ K.pickFromHistory p.1.1 p.1.2 p.2) :=
  ⟨RecursiveIn.mono hOE K.compPart_recursiveIn, K.transportPart_recursiveIn hOE,
    K.pickFromHistory_computableIn hOE⟩

end General

/-! ### A concrete two-stage chain -/

section Fixture

attribute [local instance] succStructure

/-- The fixture family: the lifted successor family with two generator widths. -/
noncomputable abbrev twoStageFamily (O : Set (ℕ →. ℕ)) : PartialAgeIn O succLang :=
  (succAgeMixed O).toPartialAge

variable (O : Set (ℕ →. ℕ))

/-- Base stage on member `0`, then a silent step: the identity data into member `0` again. -/
noncomputable def twoStages : List StageRecord :=
  [⟨0, (twoStageFamily O).idData 0⟩, ⟨0, (twoStageFamily O).idData 0⟩]

/-- **The silent step preserves the invariant.** -/
theorem test_two_stages_invariant : (twoStageFamily O).ChainInvariant (twoStages O) :=
  ((twoStageFamily O).chainInvariant_base 0).snoc
    (fun r hr ↦ by
      rw [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hr
      subst hr; rfl)
    rfl ((twoStageFamily O).idData_partialIsEmbedding 0)

/-- **Transport across the silent step halts with endpoints `0` and `0`.** -/
theorem test_two_stages_transport :
    ∃ H ∈ (twoStageFamily O).transportPart (twoStages O) 0 1,
      H.domIdx = 0 ∧ H.codIdx = 0 ∧ (twoStageFamily O).PartialIsEmbedding H :=
  (twoStageFamily O).transportPart_partialIsEmbedding (test_two_stages_invariant O)
    (Nat.zero_le 1) (rr := ⟨0, (twoStageFamily O).idData 0⟩)
    (rs := ⟨0, (twoStageFamily O).idData 0⟩) rfl rfl

/-- A carrier-valid candidate `A_1 → A_0` that is **not** an embedding: `A_1` has two recorded
generators, the range has one entry. -/
def nonactualCandidate : PotentialEmbeddingData := PotentialEmbeddingData.ofTriple (1, 0, [7])

theorem test_nonactual_candidate_carrierValid :
    (twoStageFamily O).CarrierValid (nonactualCandidate) :=
  fun _ _ ↦ by simp [twoStageFamily]

theorem test_nonactual_candidate_not_embedding :
    ¬ (twoStageFamily O).PartialIsEmbedding nonactualCandidate := by
  rintro h
  have := h.length
  simp [nonactualCandidate, twoStageFamily, ComputableAgeIn.toPartialAge, succAgeMixed] at this

/-- **Nonactual, yet it composes**: with the actual identity on `A_0`, the composite halts, has
endpoints `1` and `0`, and is carrier-valid — proved alongside nonactualness of the candidate. -/
theorem test_nonactual_candidate_composes :
    ¬ (twoStageFamily O).PartialIsEmbedding nonactualCandidate ∧
      ∃ H ∈ (twoStageFamily O).compPart ((twoStageFamily O).idData 0) nonactualCandidate,
        H.domIdx = 1 ∧ H.codIdx = 0 ∧ (twoStageFamily O).CarrierValid H :=
  ⟨test_nonactual_candidate_not_embedding O,
    (twoStageFamily O).compPart_carrierValid rfl (test_nonactual_candidate_carrierValid O)
      ((twoStageFamily O).idData_partialIsEmbedding 0)⟩

end Fixture

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.test_compPart_realizer
#assert_standard_axioms FirstOrder.Language.test_compPart_carrierValid
#assert_standard_axioms FirstOrder.Language.test_compPart_exists
#assert_standard_axioms FirstOrder.Language.test_transport_self
#assert_standard_axioms FirstOrder.Language.test_transport_succ
#assert_standard_axioms FirstOrder.Language.test_transport_lands
#assert_standard_axioms FirstOrder.Language.test_invariant_base
#assert_standard_axioms FirstOrder.Language.test_invariant_snoc
#assert_standard_axioms FirstOrder.Language.test_pick_agrees
#assert_standard_axioms FirstOrder.Language.test_effective
#assert_standard_axioms FirstOrder.Language.test_two_stages_invariant
#assert_standard_axioms FirstOrder.Language.test_two_stages_transport
#assert_standard_axioms FirstOrder.Language.test_nonactual_candidate_carrierValid
#assert_standard_axioms FirstOrder.Language.test_nonactual_candidate_not_embedding
#assert_standard_axioms FirstOrder.Language.test_nonactual_candidate_composes
