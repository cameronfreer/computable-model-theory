/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.ChainTransition
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: the clock-stage transition

**The three proofs are gated separately, on their own hypotheses.** `test_halting` takes only the
run invariant; `test_preservation` takes the invariant and membership; `test_requirement` is the
only row that assumes the decoded maps are actual embeddings. A reader can check from the signatures
alone that halting and preservation never ask the scheduled candidate to be an embedding.

**The membership specification exposes what the record does not store.** `test_spec` is the iff;
`test_both_legs_recoverable` uses it to read the right leg back off a firing step even though the
appended stage record holds only the left leg.

**The fired record moves only on a firing step.** `test_fired_record` says the record is unchanged
on the silent step and extended by exactly the selected code on a firing step.

**The candidate that must still extend the chain.** `collapsingCandidate` on the three-width
successor family sends both generators of `A_1` to the same point of `A_2`: it passes both width
equations and the `(n+1)` guard (`test_collapsing_static`), is carrier-valid, and is **not** an
embedding (`test_collapsing_not_embedding`). `test_collapsing_fires` shows that, whenever such a
candidate is the selected code, the firing step still halts and preserves the invariant — from
`stepPart_dom` and `runInvariant_of_mem`, with the candidate's nonactualness proved alongside. This
is the case the earlier width-mismatch fixture could not reach.

**Effectivity.** `test_effective` records that the transition is partial recursive in the state and
the clock, at any oracle reading the family and running the selector.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

section General

variable {K : PartialAgeIn O L} (W : PartialCAPWitness E K)

/-- **Halting**, from the run invariant alone. -/
theorem test_halting {S : RunState} {s : ℕ} (h : K.RunInvariant S s) :
    (PartialAgeIn.stepPart K W S s).Dom :=
  PartialAgeIn.stepPart_dom W h

/-- **Invariant preservation**, from the invariant and membership alone. -/
theorem test_preservation {S : RunState} {s : ℕ} (h : K.RunInvariant S s) {S' : RunState}
    (hS' : S' ∈ PartialAgeIn.stepPart K W S s) : K.RunInvariant S' (s + 1) :=
  PartialAgeIn.runInvariant_of_mem W h hS'

/-- **Requirement satisfaction** — the only row assuming actual inputs. -/
theorem test_requirement {S : RunState} {s e : ℕ} (h : K.RunInvariant S s)
    (hp : K.pickFromHistory (stageHistory S.stages) S.fired s = some e) {q : RequirementData}
    (hq : (decode e : Option RequirementData) = some q)
    (hf : K.PartialIsEmbedding (q.chainMap S.dHist)) (hg : K.PartialIsEmbedding q.targetMap) :
    ∃ δ ∈ K.transportPart S.stages q.chainStage s,
      ∃ F ∈ K.compPart δ (q.chainMap S.dHist),
        ∃ D ∈ W.sel (PotentialSpanData.ofPair (F, q.targetMap)),
          K.PartialIsEmbedding F ∧ K.PartialIsEmbedding D.rightToApex ∧
            K.PartialCommutes (PotentialSpanData.ofPair (F, q.targetMap)) D ∧
              S.capExtension e D ∈ PartialAgeIn.stepPart K W S s :=
  PartialAgeIn.exists_square_of_fire W h hp hq hf hg

/-- **The membership specification.** -/
theorem test_spec {S : RunState} {s : ℕ} {S' : RunState} :
    S' ∈ PartialAgeIn.stepPart K W S s ↔
      (K.pickFromHistory (stageHistory S.stages) S.fired s = none ∧
        S' = PartialAgeIn.identityExtension K S s) ∨
      ∃ e, K.pickFromHistory (stageHistory S.stages) S.fired s = some e ∧
        ∃ q : RequirementData, (decode e : Option RequirementData) = some q ∧
          ∃ δ ∈ K.transportPart S.stages q.chainStage s,
            ∃ F ∈ K.compPart δ (q.chainMap S.dHist),
              ∃ D ∈ W.sel (PotentialSpanData.ofPair (F, q.targetMap)),
                S' = S.capExtension e D :=
  PartialAgeIn.mem_stepPart_iff K W

/-- **Both output legs are recoverable** from a firing step, although the record stores the left
one: the right leg is the `rightToApex` of the diagram the specification exposes, and it is
well-formed by the selector's unconditional clause. -/
theorem test_both_legs_recoverable {S : RunState} {s e : ℕ} {S' : RunState}
    (hp : K.pickFromHistory (stageHistory S.stages) S.fired s = some e)
    (hS' : S' ∈ PartialAgeIn.stepPart K W S s) :
    ∃ D : AmalgamationDiagramData,
      S'.stages = S.stages ++ [⟨D.leftToApex.codIdx, D.leftToApex⟩] ∧
      K.PartialIsEmbedding D.leftToApex ∧ K.PartialWellFormed D.rightToApex ∧
        D.leftToApex.codIdx = D.rightToApex.codIdx := by
  rcases (PartialAgeIn.mem_stepPart_iff K W).1 hS' with
    ⟨hnone, -⟩ | ⟨e', hp', q, -, δ, -, F, -, D, hD, rfl⟩
  · rw [hp] at hnone; exact absurd hnone (by simp)
  · obtain ⟨hshape, hleft, hright⟩ := W.unconditional _ D hD
    exact ⟨D, rfl, hleft, hright, hshape.2.2⟩

/-- **The fired record moves only on a firing step**: unchanged on the silent step, extended by the
selected code on a firing step. -/
theorem test_fired_record {S : RunState} {s : ℕ} {S' : RunState}
    (hS' : S' ∈ PartialAgeIn.stepPart K W S s) :
    (K.pickFromHistory (stageHistory S.stages) S.fired s = none ∧ S'.fired = S.fired) ∨
      ∃ e, K.pickFromHistory (stageHistory S.stages) S.fired s = some e ∧
        S'.fired = S.fired ++ [e] := by
  rcases (PartialAgeIn.mem_stepPart_iff K W).1 hS' with
    ⟨hnone, rfl⟩ | ⟨e, hp, -, -, -, -, -, -, D, -, rfl⟩
  · exact Or.inl ⟨hnone, rfl⟩
  · exact Or.inr ⟨e, hp, rfl⟩

/-- **Effectivity** of the transition, with `O ⊆ E` appearing only here. -/
theorem test_effective (hOE : O ⊆ E) :
    RecursiveIn E fun p : RunState × ℕ ↦ PartialAgeIn.stepPart K W p.1 p.2 :=
  PartialAgeIn.stepPart_recursiveIn W hOE

/-- The initial state satisfies the invariant at clock `0`. -/
theorem test_init (i : ℕ) : K.RunInvariant (RunState.init K i) 0 :=
  K.runInvariant_init i

end General

/-! ### The candidate that must still extend the chain -/

section Fixture

attribute [local instance] succStructure

/-- The three-width successor family in the general setting. -/
noncomputable abbrev threeWidthFamily (O : Set (ℕ →. ℕ)) : PartialAgeIn O succLang :=
  (succAgeMixed O).toPartialAge

/-- A requirement from `A_1` (two generators) into `A_2` (three generators): the chain map sends
both generators of `A_1` to `0` in the member recorded at stage `0`, and the target map is the
inclusion `[0, 1]`. Both width equations hold and the `(n+1)` guard holds; the chain map is not an
embedding. -/
def collapsingCandidate : RequirementData := ⟨1, 0, 2, [0, 0], [0, 1]⟩

variable (O : Set (ℕ →. ℕ))

/-- **Passes the static guards**: widths `2 = 2`, `2 = 2`, and `3 = 2 + 1`. -/
theorem test_collapsing_static : (threeWidthFamily O).StaticAdmissible collapsingCandidate := by
  simp [PartialAgeIn.StaticAdmissible, collapsingCandidate, threeWidthFamily,
    ComputableAgeIn.toPartialAge, succAgeMixed]

/-- **Carrier-valid** in any member (the lifted family has full carriers). -/
theorem test_collapsing_carrierValid (d : ℕ → ℕ) :
    (threeWidthFamily O).CarrierValid (collapsingCandidate.chainMap d) ∧
      (threeWidthFamily O).CarrierValid collapsingCandidate.targetMap :=
  ⟨fun _ _ ↦ by simp [threeWidthFamily], fun _ _ ↦ by simp [threeWidthFamily]⟩

/-- **Not an embedding**: both generators of `A_1` go to `0`, but an embedding is injective and the
generators `0` and `1` of `A_1` are distinct. -/
theorem test_collapsing_not_embedding (d : ℕ → ℕ) :
    ¬ (threeWidthFamily O).PartialIsEmbedding (collapsingCandidate.chainMap d) := by
  rintro ⟨f, hf⟩
  have hf' : PartialAgeIn.PartialRealizesBetween (threeWidthFamily O) (threeWidthFamily O)
      (collapsingCandidate.chainMap d) f := hf
  have hg : (threeWidthFamily O).gens (collapsingCandidate.chainMap d).domIdx = [0, 1] := by
    simp [threeWidthFamily, ComputableAgeIn.toPartialAge, succAgeMixed, collapsingCandidate]
  have hmem : ∀ n : ℕ,
      n ∈ ((threeWidthFamily O).memberAt (collapsingCandidate.chainMap d).domIdx).domain :=
    fun n ↦ by simp [threeWidthFamily]
  have h0 := PartialAgeIn.getElem?_of_realizes hf' (k := 0) (x := ⟨0, hmem 0⟩) (by rw [hg]; rfl)
  have h1 := PartialAgeIn.getElem?_of_realizes hf' (k := 1) (x := ⟨1, hmem 1⟩) (by rw [hg]; rfl)
  change ([0, 0] : Tuple ℕ)[0]? = some _ at h0
  change ([0, 0] : Tuple ℕ)[1]? = some _ at h1
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h0 h1
  have hinj := f.injective (Subtype.ext (h0.symm.trans h1) : f ⟨0, hmem 0⟩ = f ⟨1, hmem 1⟩)
  have hval : (0 : ℕ) = 1 := congrArg Subtype.val hinj
  exact absurd hval (by decide)

/-- **It still extends the chain.** Whenever the collapsing candidate is the selected code at a
stage satisfying the invariant, the transition halts and the result satisfies the invariant at the
next clock — proved from the two theorems that never ask for actualness, with nonactualness
alongside. -/
theorem test_collapsing_fires (W : PartialCAPWitness E (threeWidthFamily O)) {S : RunState}
    {s e : ℕ}
    (h : (threeWidthFamily O).RunInvariant S s)
    (hp : (threeWidthFamily O).pickFromHistory (stageHistory S.stages) S.fired s = some e)
    (he : (decode e : Option RequirementData) = some collapsingCandidate) :
    ¬ (threeWidthFamily O).PartialIsEmbedding (collapsingCandidate.chainMap S.dHist) ∧
      (PartialAgeIn.stepPart (threeWidthFamily O) W S s).Dom ∧
        ∀ S' ∈ PartialAgeIn.stepPart (threeWidthFamily O) W S s,
          (threeWidthFamily O).RunInvariant S' (s + 1) ∧ S'.fired = S.fired ++ [e] := by
  refine ⟨test_collapsing_not_embedding O S.dHist, PartialAgeIn.stepPart_dom W h, fun S' hS' ↦
    ⟨PartialAgeIn.runInvariant_of_mem W h hS', ?_⟩⟩
  rcases test_fired_record W hS' with ⟨hnone, -⟩ | ⟨e', hp', hfired⟩
  · rw [hp] at hnone; exact absurd hnone (by simp)
  · rw [hp] at hp'; obtain rfl := Option.some.inj hp'; exact hfired

end Fixture

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.test_halting
#assert_standard_axioms FirstOrder.Language.test_preservation
#assert_standard_axioms FirstOrder.Language.test_requirement
#assert_standard_axioms FirstOrder.Language.test_spec
#assert_standard_axioms FirstOrder.Language.test_both_legs_recoverable
#assert_standard_axioms FirstOrder.Language.test_fired_record
#assert_standard_axioms FirstOrder.Language.test_effective
#assert_standard_axioms FirstOrder.Language.test_init
#assert_standard_axioms FirstOrder.Language.test_collapsing_static
#assert_standard_axioms FirstOrder.Language.test_collapsing_carrierValid
#assert_standard_axioms FirstOrder.Language.test_collapsing_not_embedding
#assert_standard_axioms FirstOrder.Language.test_collapsing_fires
