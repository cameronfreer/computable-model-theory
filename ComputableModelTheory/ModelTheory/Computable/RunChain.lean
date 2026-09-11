/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.ChainAssembly
import ComputableModelTheory.ModelTheory.Computable.ChainRun

/-!
# The c.e. structure chain of the constructed run (item 4)

The run's recorded stages supply exactly the input of the generic assembly: `memberIdx K W i` is the
member-index function, and `runStep K W i n` is the connecting map recorded at stage `n + 1` — an
actual embedding from the member at `n` into the member at `n + 1`, by the run invariant. Both are
computable at any oracle reading the family and running the selector, from `run_computableIn`.
`runChain` is the assembled `CeStructureChainIn`, asking only that the base member be nonempty.

**Transport identification, after assembly.** `transportPart_eq_foldData` identifies the finite
transport computed off the run's recorded prefix with the assembly's fold — the recorded prefix is
persistent, so the prefix read at any later clock gives the same data — and
`mem_transportTo_iff_transportPart` then reads the chain's carrier transport as the application of
that data. Nothing in the run consumed the chain's transport; the identification is a theorem about
the finished object.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

namespace PartialAgeIn

variable (K : PartialAgeIn O L) (W : PartialCAPWitness E K) (i : ℕ)

/-! ### The recorded connecting maps -/

/-- The connecting map recorded at stage `n + 1`, from the member at `n` into the member at `n + 1`.
The default is never reached under the invariant. -/
noncomputable def runStep (n : ℕ) : PotentialEmbeddingData :=
  (((run K W i (n + 1)).stages[n + 1]?).map StageRecord.step).getD (K.idData (memberIdx K W i n))

variable {K W i}

theorem runStep_eq {n : ℕ} {rec : StageRecord} (h : (run K W i (n + 1)).stages[n + 1]? = some rec) :
    runStep K W i n = rec.step := by
  rw [runStep, h]; rfl

theorem memberIdx_zero : memberIdx K W i 0 = i := by
  rw [memberIdx, run_zero]; rfl

/-- The member at stage `n`, read off any clock `≥ n`. -/
theorem memberIdx_eq {n s : ℕ} {rec : StageRecord} (hns : n ≤ s)
    (h : (run K W i s).stages[n]? = some rec) : memberIdx K W i n = rec.memberIdx := by
  have := history_agrees (K := K) (W := W) (i := i) s n hns
  rw [stageHistory_getElem?, h] at this
  exact (Option.some.inj this).symm

theorem runStep_domIdx (n : ℕ) : (runStep K W i n).domIdx = memberIdx K W i n := by
  obtain ⟨rec, hrec⟩ := (run_runInvariant (K := K) (W := W) (i := i) (n + 1)).exists_getElem? le_rfl
  obtain ⟨rec₀, hrec₀⟩ :=
    (run_runInvariant (K := K) (W := W) (i := i) (n + 1)).exists_getElem? (Nat.le_succ n)
  rw [runStep_eq hrec, (run_runInvariant (n + 1)).chain.step_domIdx n rec₀ rec hrec₀ hrec,
    memberIdx_eq (Nat.le_succ n) hrec₀]

theorem runStep_codIdx (n : ℕ) : (runStep K W i n).codIdx = memberIdx K W i (n + 1) := by
  obtain ⟨rec, hrec⟩ := (run_runInvariant (K := K) (W := W) (i := i) (n + 1)).exists_getElem? le_rfl
  rw [runStep_eq hrec, (run_runInvariant (n + 1)).chain.step_codIdx rec (List.mem_of_getElem? hrec),
    memberIdx_eq le_rfl hrec]

theorem runStep_isEmbedding (n : ℕ) : K.PartialIsEmbedding (runStep K W i n) := by
  obtain ⟨rec, hrec⟩ := (run_runInvariant (K := K) (W := W) (i := i) (n + 1)).exists_getElem? le_rfl
  rw [runStep_eq hrec]
  exact (run_runInvariant (n + 1)).chain.step_isEmbedding rec (List.mem_of_getElem? hrec)

variable (K W i)

/-- **The run as assembly input.** -/
noncomputable def runChainData : K.EmbeddingChainData where
  d := memberIdx K W i
  step := runStep K W i
  step_domIdx := runStep_domIdx
  step_codIdx := runStep_codIdx
  step_isEmbedding := runStep_isEmbedding

@[simp] theorem runChainData_d : (runChainData K W i).d = memberIdx K W i := rfl
@[simp] theorem runChainData_step : (runChainData K W i).step = runStep K W i := rfl

/-! ### Effectivity -/

theorem memberIdx_computableIn (hOE : O ⊆ E) : ComputableIn E (memberIdx K W i) := by
  have hrun := run_computableIn (K := K) (W := W) (i := i) hOE
  have hhist : ComputableIn E fun s ↦ stageHistory (run K W i s).stages :=
    ComputableIn.comp (α := ℕ) (β := RunState) (σ := List ℕ)
      (f := fun S ↦ stageHistory S.stages) (g := run K W i)
      (ComputableIn.comp (α := RunState) (β := List StageRecord) (σ := List ℕ)
        (f := stageHistory) (g := RunState.stages) stageHistory_computableIn
        (RunState.primrec_stages.to_comp.computableIn (O := E))) hrun
  exact ComputableIn₂.comp (α := ℕ) (β := List ℕ) (γ := ℕ) (σ := ℕ) (f := fun l n ↦ l.getD n 0)
    (g := fun s ↦ stageHistory (run K W i s).stages) (h := fun s ↦ s)
    ((Primrec.list_getD (0 : ℕ)).to_comp.computableIn₂ (O := E)) hhist ComputableIn.id

theorem runStep_computableIn (hOE : O ⊆ E) : ComputableIn E (runStep K W i) := by
  have hrun := run_computableIn (K := K) (W := W) (i := i) hOE
  have hsucc : ComputableIn E fun n : ℕ ↦ n + 1 := Primrec.succ.to_comp.computableIn (O := E)
  have hstages : ComputableIn E fun n : ℕ ↦ (run K W i (n + 1)).stages :=
    ComputableIn.comp (α := ℕ) (β := RunState) (σ := List StageRecord) (f := RunState.stages)
      (g := fun n ↦ run K W i (n + 1)) (RunState.primrec_stages.to_comp.computableIn (O := E))
      (ComputableIn.comp (α := ℕ) (β := ℕ) (σ := RunState) (f := run K W i) (g := fun n ↦ n + 1)
        hrun hsucc)
  have hget : ComputableIn E fun n : ℕ ↦ (run K W i (n + 1)).stages[n + 1]? :=
    ComputableIn₂.comp (α := ℕ) (β := List StageRecord) (γ := ℕ) (σ := Option StageRecord)
      (f := fun l k ↦ l[k]?) (g := fun n ↦ (run K W i (n + 1)).stages) (h := fun n ↦ n + 1)
      (Computable.list_getElem?.computableIn₂ (O := E)) hstages hsucc
  have hmap : ComputableIn E fun n : ℕ ↦
      ((run K W i (n + 1)).stages[n + 1]?).map StageRecord.step :=
    ComputableIn.option_map (α := ℕ) (β := StageRecord) (σ := PotentialEmbeddingData)
      (f := fun n ↦ (run K W i (n + 1)).stages[n + 1]?) (g := fun _ rec ↦ rec.step) hget
      (ComputableIn.comp (α := ℕ × StageRecord) (β := StageRecord) (σ := PotentialEmbeddingData)
        (f := StageRecord.step) (g := fun p ↦ p.2)
        (StageRecord.primrec_step.to_comp.computableIn (O := E)) ComputableIn.snd).to₂
  have hdef : ComputableIn E fun n : ℕ ↦ K.idData (memberIdx K W i n) :=
    ComputableIn.comp (α := ℕ) (β := ℕ) (σ := PotentialEmbeddingData) (f := K.idData)
      (g := memberIdx K W i) (K.idData_computableIn hOE) (memberIdx_computableIn K W i hOE)
  exact (ComputableIn.option_getD (α := ℕ) (β := PotentialEmbeddingData)
    (f := fun n ↦ ((run K W i (n + 1)).stages[n + 1]?).map StageRecord.step)
    (g := fun n ↦ K.idData (memberIdx K W i n)) hmap hdef).of_eq fun _ ↦ rfl

/-! ### The chain -/

theorem domainAt_memberIdx_zero_nonempty (h0 : (K.domainAt i).Nonempty) :
    (K.domainAt ((runChainData K W i).d 0)).Nonempty := by
  rw [runChainData_d, memberIdx_zero]; exact h0

/-- **The c.e. structure chain of the run**, at the map oracle. -/
noncomputable def runChain (hOE : O ⊆ E) (h0 : (K.domainAt i).Nonempty) : CeStructureChainIn E L :=
  (runChainData K W i).toChain (domainAt_memberIdx_zero_nonempty K W i h0) hOE
    (memberIdx_computableIn K W i hOE) (runStep_computableIn K W i hOE)

theorem runChain_stage_domain (hOE : O ⊆ E) (h0 : (K.domainAt i).Nonempty) (n : ℕ) :
    ((runChain K W i hOE h0).stageAt n).domain = K.domainAt (memberIdx K W i n) :=
  (runChainData K W i).toChain_stage_domain _ hOE _ _ n

theorem runChain_step (hOE : O ⊆ E) (h0 : (K.domainAt i).Nonempty) (n : ℕ) (x : ℕ) :
    (runChain K W i hOE h0).step n x = K.applyPotentialPart (runStep K W i n) x := rfl

theorem runChain_uniformEvaluators (hOE : O ⊆ E) (h0 : (K.domainAt i).Nonempty) :
    (runChain K W i hOE h0).UniformEvaluatorsIn :=
  (runChainData K W i).toChain_uniformEvaluators _ hOE _ _

/-! ### Transport identification -/

variable {K W i}

/-- Steps between two recorded stages read the same off any prefix long enough to contain them. -/
theorem stepsBetween_eq_of_prefix {l₁ l₂ : List StageRecord} (h : l₁ <+: l₂) {r s : ℕ}
    (hs : s < l₁.length) : stepsBetween l₁ r s = stepsBetween l₂ r s := by
  obtain ⟨t, rfl⟩ := h
  unfold stepsBetween
  rcases le_or_gt r s with hrs | hrs
  · rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length]
    rw [List.length_drop]; omega
  · rw [Nat.sub_eq_zero_of_le hrs.le, List.take_zero, List.take_zero]

/-- The finite transport between recorded stages `r ≤ s` is the same off the prefix at every clock
`≥ s`. -/
theorem transportPart_run_eq {r s t : ℕ} (hrs : r ≤ s) (hst : s ≤ t) :
    K.transportPart (run K W i t).stages r s = K.transportPart (run K W i s).stages r s := by
  unfold transportPart
  rw [stepsBetween_eq_of_prefix (run_stages_prefix hst) (by rw [run_stages_length]; omega)]
  congr 2
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, stageHistory_getElem?,
    stageHistory_getElem?, run_getElem?_eq (le_trans hrs hst), run_getElem?_eq hrs]

/-- **The recorded transport is the assembly's fold.** -/
theorem transportPart_eq_foldData (r : ℕ) : ∀ k : ℕ,
    K.transportPart (run K W i (r + k)).stages r (r + k) = (runChainData K W i).foldData r k
  | 0 => by
    rw [Nat.add_zero, K.transportPart_self, EmbeddingChainData.foldData_zero]
    rfl
  | k + 1 => by
    obtain ⟨rec, hrec⟩ :=
      (run_runInvariant (K := K) (W := W) (i := i) (r + k + 1)).exists_getElem? le_rfl
    rw [← Nat.add_assoc, K.transportPart_succ _ (Nat.le_add_right r k) hrec,
      transportPart_run_eq (Nat.le_add_right r k) (Nat.le_succ _), transportPart_eq_foldData r k,
      EmbeddingChainData.foldData_succ, runChainData_step, runStep_eq hrec]

/-- **Transport identification on the run**: for `r ≤ s` and a point of the member at `r`, the
chain's carrier transport from `r` to `s` is the application of the transport data recorded off the
run's prefix at `s`. -/
theorem mem_transportTo_iff_transportPart (hOE : O ⊆ E) (h0 : (K.domainAt i).Nonempty) {r s : ℕ}
    (hrs : r ≤ s) {δ : PotentialEmbeddingData} (hδ : δ ∈ K.transportPart (run K W i s).stages r s)
    {x y : ℕ} (hx : x ∈ K.domainAt (memberIdx K W i r)) :
    y ∈ (runChain K W i hOE h0).transportTo r s x ↔ y ∈ K.applyPotentialPart δ x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hrs
  rw [transportPart_eq_foldData] at hδ
  exact (runChainData K W i).mem_transportTo_iff_applyPotentialPart _ hOE _ _ r k hδ hx

end PartialAgeIn

end FirstOrder.Language
