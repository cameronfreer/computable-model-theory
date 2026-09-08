/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.ChainHistory
import ComputableModelTheory.ModelTheory.Computable.PartialCAP

/-!
# The clock-stage transition of Theorem 3.9's construction

One step of the recorded chain, `Part`-valued. At clock stage `s` the state is the recorded prefix
`[d 0, …, d s]` with its connecting maps and the fired record. The transition selects the least
available unfired code through the history (`pickFromHistory`); on **no selection** it appends the
identity data at the current member and leaves the fired record unchanged; on a selection `e`
decoding to `q = (i, r, k, f, g)` it

1. binds the finite transport `δ_{r,s}` off the recorded prefix,
2. binds the transported candidate `δ_{r,s} ∘ f` (`compPart`),
3. forms the current span `⟨δ_{r,s} ∘ f, g⟩` and binds the supplied CAP selector,
4. appends the returned **left leg** as the connecting map into the apex, and appends `e` to the
   fired record — both inside the same successful return.

`mem_stepPart_iff` is the membership specification: it exposes the decoded requirement, the
transport, the transported span, and the CAP output membership, so later proofs can recover *both*
output legs even though the stage record stores only the left one.

## Three proofs, kept separate

* **Halting** (`stepPart_dom`): from carrier validity of the selected candidate (supplied by
  availability) and actualness of the chain transport (supplied by the run invariant), through
  `compPart_carrierValid` and the selector's halting clause. Nothing here asks the scheduled
  candidate to be an embedding.
* **Invariant preservation** (`runInvariant_of_mem`): from the selector's **unconditional** left
  actualness and well-shapedness. Again no actualness of the candidate is used.
* **Requirement satisfaction** (`exists_square_of_fire`): when the decoded maps *are* actual, the
  transported span is actual, and the selector's **conditional** soundness gives an actual right leg
  and a commuting square.

The **run invariant** carries `stages.length = s + 1` besides `ChainInvariant`: this ties the
recorded prefix to the clock, makes every history lookup at a stage `≤ s` hit a record, and
identifies the current member with the last record.

Both branches stay in `Part`; totalizing the run is a later theorem (item 3(d)), proved from the
halting theorem here.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-! ### A CAP witness, unbundled from `PartialCAPIn` -/

/-- The data of a `PartialCAPIn E K` witness, as a structure: the selector and its four clauses. -/
structure PartialCAPWitness (E : Set (ℕ →. ℕ)) (K : PartialAgeIn O L) where
  /-- The partial selector. -/
  sel : PotentialSpanData →. AmalgamationDiagramData
  /-- The selector is partial recursive in the witness oracle. -/
  recursiveIn : RecursiveIn E sel
  /-- A carrier-valid span forces convergence. -/
  halts : ∀ S : PotentialSpanData, K.CarrierValidSpan S → (sel S).Dom
  /-- Any returned diagram is well-shaped, with actual left leg and well-formed right leg. -/
  unconditional : ∀ (S : PotentialSpanData) (D : AmalgamationDiagramData), D ∈ sel S →
    D.WellShapedFor S ∧ K.PartialIsEmbedding D.leftToApex ∧ K.PartialWellFormed D.rightToApex
  /-- On an actual span, the right leg is actual and the square commutes. -/
  sound : ∀ (S : PotentialSpanData) (D : AmalgamationDiagramData), D ∈ sel S →
    K.PartialSpanActual S → K.PartialIsEmbedding D.rightToApex ∧ K.PartialCommutes S D

/-- `PartialCAPIn` supplies a witness. -/
theorem PartialAgeIn.PartialCAPIn.nonempty_witness {K : PartialAgeIn O L}
    (h : K.PartialCAPIn E) : Nonempty (PartialCAPWitness E K) := by
  obtain ⟨sel, hsel, hhalt, huncond, hsound⟩ := h
  exact ⟨⟨sel, hsel, hhalt, huncond, hsound⟩⟩

/-- A witness is a `PartialCAPIn`. -/
theorem PartialCAPWitness.partialCAPIn {K : PartialAgeIn O L} (W : PartialCAPWitness E K) :
    K.PartialCAPIn E :=
  ⟨W.sel, W.recursiveIn, W.halts, W.unconditional, W.sound⟩

/-! ### The run state -/

/-- The state of the run: the recorded stages and the fired record. Proof-free. -/
structure RunState where
  /-- The recorded stages `d 0, …, d s` with their connecting maps. -/
  stages : List StageRecord
  /-- The codes fired so far, in firing order. -/
  fired : List ℕ

/-- The code-level packaging of run states. -/
private def rsEquiv : RunState ≃ List StageRecord × List ℕ where
  toFun S := (S.stages, S.fired)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable RunState :=
  Primcodable.ofEquiv _ rsEquiv

namespace RunState

theorem primrec_stages : Primrec stages :=
  (Primrec.fst.comp (Primrec.of_equiv (e := rsEquiv))).of_eq fun _ ↦ rfl

theorem primrec_fired : Primrec fired :=
  (Primrec.snd.comp (Primrec.of_equiv (e := rsEquiv))).of_eq fun _ ↦ rfl

/-- The member-index lookup read off the state's history, with default `0` past its end. -/
def dHist (S : RunState) (r : ℕ) : ℕ :=
  (stageHistory S.stages).getD r 0

/-- The current member at clock stage `s`: the history read at `s`. -/
def currentMember (S : RunState) (s : ℕ) : ℕ := S.dHist s

/-- **The firing step's result**: append the returned left leg as the connecting map into the apex,
and the fired code to the record. -/
def capExtension (S : RunState) (e : ℕ) (D : AmalgamationDiagramData) : RunState :=
  ⟨S.stages ++ [⟨D.leftToApex.codIdx, D.leftToApex⟩], S.fired ++ [e]⟩

theorem fired_capExtension (S : RunState) (e : ℕ) (D : AmalgamationDiagramData) :
    (S.capExtension e D).fired = S.fired ++ [e] := rfl

theorem stages_capExtension (S : RunState) (e : ℕ) (D : AmalgamationDiagramData) :
    (S.capExtension e D).stages = S.stages ++ [⟨D.leftToApex.codIdx, D.leftToApex⟩] := rfl

/-- The initial state: one stage on member `i`, nothing fired. -/
def init (K : PartialAgeIn O L) (i : ℕ) : RunState :=
  ⟨[⟨i, K.idData i⟩], []⟩

end RunState

namespace PartialAgeIn

variable (K : PartialAgeIn O L)

/-! ### The run invariant -/

/-- **The run invariant** at clock stage `s`: the recorded prefix satisfies the chain invariant and
has exactly `s + 1` stages. -/
structure RunInvariant (S : RunState) (s : ℕ) : Prop where
  /-- The chain invariant on the recorded prefix. -/
  chain : K.ChainInvariant S.stages
  /-- The prefix records exactly stages `0, …, s`. -/
  length : S.stages.length = s + 1

theorem runInvariant_init (i : ℕ) : K.RunInvariant (RunState.init K i) 0 :=
  ⟨K.chainInvariant_base i, rfl⟩

variable {K}

/-- Under the invariant every stage `≤ s` is recorded. -/
theorem RunInvariant.exists_getElem? {S : RunState} {s : ℕ} (h : K.RunInvariant S s) {r : ℕ}
    (hr : r ≤ s) : ∃ rec, S.stages[r]? = some rec :=
  ⟨_, List.getElem?_eq_getElem (by rw [h.length]; omega)⟩

/-- Under the invariant the history lookup at a recorded stage is that stage's member. -/
theorem RunInvariant.dHist_eq {S : RunState} {s : ℕ} (_ : K.RunInvariant S s) {r : ℕ}
    {rec : StageRecord} (hrec : S.stages[r]? = some rec) : S.dHist r = rec.memberIdx := by
  rw [RunState.dHist, List.getD_eq_getElem?_getD, stageHistory_getElem?, hrec]; rfl

/-- Under the invariant the last record is the record at stage `s`. -/
theorem RunInvariant.getLast?_eq {S : RunState} {s : ℕ} (h : K.RunInvariant S s) :
    S.stages.getLast? = S.stages[s]? := by
  rw [List.getLast?_eq_getElem?, h.length, Nat.add_sub_cancel]

variable (K)

/-! ### The transition -/

variable (W : PartialCAPWitness E K)

/-- **The silent step**: append the identity data at the current member; the fired record is
unchanged. -/
def identityExtension (S : RunState) (s : ℕ) : RunState :=
  ⟨S.stages ++ [⟨S.currentMember s, K.idData (S.currentMember s)⟩], S.fired⟩

/-- **The firing step** on code `e`: decode, transport, compose, amalgamate, extend. `Part`-valued
at every stage; halting is the theorem `stepPart_dom`. -/
noncomputable def firePart (S : RunState) (s e : ℕ) : Part RunState :=
  ((decode e : Option RequirementData) : Part RequirementData).bind fun q ↦
    (K.transportPart S.stages q.chainStage s).bind fun δ ↦
      (K.compPart δ (q.chainMap S.dHist)).bind fun F ↦
        (W.sel (PotentialSpanData.ofPair (F, q.targetMap))).map fun D ↦ S.capExtension e D

/-- **The clock-stage transition**: select through the history; fire on a selection, otherwise the
silent step. -/
noncomputable def stepPart (S : RunState) (s : ℕ) : Part RunState :=
  Option.casesOn (motive := fun _ ↦ Part RunState)
    (K.pickFromHistory (stageHistory S.stages) S.fired s)
    (Part.some (identityExtension K S s)) (firePart K W S s)

/-- **Membership in the firing step**, unfolded to its four components. -/
theorem mem_firePart_iff {S : RunState} {s e : ℕ} {S' : RunState} :
    S' ∈ firePart K W S s e ↔
      ∃ q : RequirementData, (decode e : Option RequirementData) = some q ∧
        ∃ δ ∈ K.transportPart S.stages q.chainStage s,
          ∃ F ∈ K.compPart δ (q.chainMap S.dHist),
            ∃ D ∈ W.sel (PotentialSpanData.ofPair (F, q.targetMap)),
              S' = S.capExtension e D := by
  unfold firePart
  rcases hq : (decode e : Option RequirementData) with _ | q
  · simp
  · simp only [Part.coe_some, Part.bind_some, Part.mem_bind_iff, Part.mem_map_iff,
      Option.some.injEq, exists_eq_left', eq_comm]

/-- **The membership specification of the transition.** Either no code is selected and the result is
the silent step, or a code `e` is selected, decodes to `q`, the transport `δ_{r,s}` halts, the
transported candidate halts, the selector returns `D` on the span `⟨δ ∘ f, g⟩`, and the result
records `D`'s left leg and fires `e`. -/
theorem mem_stepPart_iff {S : RunState} {s : ℕ} {S' : RunState} :
    S' ∈ stepPart K W S s ↔
      (K.pickFromHistory (stageHistory S.stages) S.fired s = none ∧
        S' = identityExtension K S s) ∨
      ∃ e, K.pickFromHistory (stageHistory S.stages) S.fired s = some e ∧
        ∃ q : RequirementData, (decode e : Option RequirementData) = some q ∧
          ∃ δ ∈ K.transportPart S.stages q.chainStage s,
            ∃ F ∈ K.compPart δ (q.chainMap S.dHist),
              ∃ D ∈ W.sel (PotentialSpanData.ofPair (F, q.targetMap)),
                S' = S.capExtension e D := by
  unfold stepPart
  rcases hp : K.pickFromHistory (stageHistory S.stages) S.fired s with _ | e
  · simp only [Part.mem_some_iff, true_and, reduceCtorEq, false_and, exists_false, or_false]
  · simp only [reduceCtorEq, false_and, Option.some.injEq, false_or]
    rw [mem_firePart_iff]
    constructor
    · intro h; exact ⟨e, rfl, h⟩
    · rintro ⟨e', rfl, h⟩; exact h

/-! ### Effectivity

Every combinator below is pinned on its implicit type and function parameters: the state is an
`ofEquiv`-encoded structure, and an unpinned composition through it swamps `whnf`. -/

section Effectivity

variable {K}

private theorem stages_computableIn : ComputableIn E RunState.stages :=
  RunState.primrec_stages.to_comp.computableIn

private theorem fired_computableIn : ComputableIn E RunState.fired :=
  RunState.primrec_fired.to_comp.computableIn

private theorem history_computableIn : ComputableIn E fun S : RunState ↦ stageHistory S.stages :=
  ComputableIn.comp (α := RunState) (β := List StageRecord) (σ := List ℕ) (f := stageHistory)
    (g := RunState.stages) stageHistory_computableIn stages_computableIn

private theorem dHist_computableIn : ComputableIn E fun p : RunState × ℕ ↦ p.1.dHist p.2 :=
  ComputableIn₂.comp (α := RunState × ℕ) (β := List ℕ) (γ := ℕ) (σ := ℕ)
    (f := fun l n ↦ l.getD n 0) (g := fun p ↦ stageHistory p.1.stages) (h := fun p ↦ p.2)
    ((Primrec.list_getD (0 : ℕ)).to_comp.computableIn₂ (O := E))
    (ComputableIn.comp (α := RunState × ℕ) (β := RunState) (σ := List ℕ)
      (f := fun S ↦ stageHistory S.stages) (g := fun p ↦ p.1) history_computableIn
      ComputableIn.fst)
    ComputableIn.snd

private theorem pick_computableIn (hOE : O ⊆ E) : ComputableIn E fun p : RunState × ℕ ↦
    K.pickFromHistory (stageHistory p.1.stages) p.1.fired p.2 :=
  ComputableIn.comp (α := RunState × ℕ) (β := (List ℕ × List ℕ) × ℕ) (σ := Option ℕ)
    (f := fun x ↦ K.pickFromHistory x.1.1 x.1.2 x.2)
    (g := fun p ↦ ((stageHistory p.1.stages, p.1.fired), p.2)) (K.pickFromHistory_computableIn hOE)
    (ComputableIn.pair (α := RunState × ℕ) (β := List ℕ × List ℕ) (γ := ℕ)
      (f := fun p ↦ (stageHistory p.1.stages, p.1.fired)) (g := fun p ↦ p.2)
      (ComputableIn.pair (α := RunState × ℕ) (β := List ℕ) (γ := List ℕ)
        (f := fun p ↦ stageHistory p.1.stages) (g := fun p ↦ p.1.fired)
        (ComputableIn.comp (α := RunState × ℕ) (β := RunState) (σ := List ℕ)
          (f := fun S ↦ stageHistory S.stages) (g := fun p ↦ p.1) history_computableIn
          ComputableIn.fst)
        (ComputableIn.comp (α := RunState × ℕ) (β := RunState) (σ := List ℕ)
          (f := RunState.fired) (g := fun p ↦ p.1) fired_computableIn ComputableIn.fst))
      ComputableIn.snd)

/-- A stage record from computable components, crossing the encoding. -/
private theorem stageRecord_computableIn {α : Type*} [Primcodable α] {m : α → ℕ}
    {F : α → PotentialEmbeddingData} (hm : ComputableIn E m) (hF : ComputableIn E F) :
    ComputableIn E fun a ↦ (⟨m a, F a⟩ : StageRecord) :=
  ComputableIn.encode_iff.1
    ((ComputableIn.encode.comp (ComputableIn.pair (α := α) (β := ℕ) (γ := PotentialEmbeddingData)
      (f := m) (g := F) hm hF)).of_eq fun _ ↦ rfl)

/-- A run state from computable components, crossing the encoding. -/
private theorem runState_computableIn {α : Type*} [Primcodable α] {l : α → List StageRecord}
    {r : α → List ℕ} (hl : ComputableIn E l) (hr : ComputableIn E r) :
    ComputableIn E fun a ↦ (⟨l a, r a⟩ : RunState) :=
  ComputableIn.encode_iff.1
    ((ComputableIn.encode.comp (ComputableIn.pair (α := α) (β := List StageRecord) (γ := List ℕ)
      (f := l) (g := r) hl hr)).of_eq fun _ ↦ rfl)

/-- Potential embedding data from computable components, crossing the encoding. -/
private theorem ofTriple_computableIn' {α : Type*} [Primcodable α] {a b : α → ℕ}
    {t : α → Tuple ℕ} (ha : ComputableIn E a) (hb : ComputableIn E b) (ht : ComputableIn E t) :
    ComputableIn E fun x ↦ PotentialEmbeddingData.ofTriple (a x, b x, t x) :=
  ComputableIn.encode_iff.1
    ((ComputableIn.encode.comp (ComputableIn.pair (α := α) (β := ℕ) (γ := ℕ × Tuple ℕ)
      (f := a) (g := fun x ↦ (b x, t x)) ha
      (ComputableIn.pair (α := α) (β := ℕ) (γ := Tuple ℕ) (f := b) (g := t) hb ht))).of_eq
      fun _ ↦ rfl)

private theorem identityExtension_computableIn (hOE : O ⊆ E) :
    ComputableIn E fun p : RunState × ℕ ↦ identityExtension K p.1 p.2 := by
  have hcur : ComputableIn E fun p : RunState × ℕ ↦ p.1.currentMember p.2 := dHist_computableIn
  have hrec : ComputableIn E fun p : RunState × ℕ ↦
      (⟨p.1.currentMember p.2, K.idData (p.1.currentMember p.2)⟩ : StageRecord) :=
    stageRecord_computableIn hcur
      (ComputableIn.comp (α := RunState × ℕ) (β := ℕ) (σ := PotentialEmbeddingData) (f := K.idData)
        (g := fun p ↦ p.1.currentMember p.2) (K.idData_computableIn hOE) hcur)
  have hl : ComputableIn E fun p : RunState × ℕ ↦
      p.1.stages ++ [(⟨p.1.currentMember p.2, K.idData (p.1.currentMember p.2)⟩ : StageRecord)] :=
    ComputableIn₂.comp (α := RunState × ℕ) (β := List StageRecord) (γ := StageRecord)
      (σ := List StageRecord) (f := fun l a ↦ l ++ [a]) (g := fun p ↦ p.1.stages)
      (h := fun p ↦ ⟨p.1.currentMember p.2, K.idData (p.1.currentMember p.2)⟩)
      (Computable.list_concat.computableIn₂ (O := E))
      (ComputableIn.comp (α := RunState × ℕ) (β := RunState) (σ := List StageRecord)
        (f := RunState.stages) (g := fun p ↦ p.1) stages_computableIn ComputableIn.fst)
      hrec
  exact runState_computableIn hl
    (ComputableIn.comp (α := RunState × ℕ) (β := RunState) (σ := List ℕ) (f := RunState.fired)
      (g := fun p ↦ p.1) fired_computableIn ComputableIn.fst)

private theorem capExtension_computableIn :
    ComputableIn E fun q : (RunState × ℕ) × AmalgamationDiagramData ↦
      q.1.1.capExtension q.1.2 q.2 := by
  have hleft : ComputableIn E fun q : (RunState × ℕ) × AmalgamationDiagramData ↦
      q.2.leftToApex :=
    ComputableIn.comp (α := (RunState × ℕ) × AmalgamationDiagramData)
      (β := AmalgamationDiagramData) (σ := PotentialEmbeddingData)
      (f := AmalgamationDiagramData.leftToApex) (g := fun q ↦ q.2)
      AmalgamationDiagramData.leftToApex_computable ComputableIn.snd
  have hrec : ComputableIn E fun q : (RunState × ℕ) × AmalgamationDiagramData ↦
      (⟨q.2.leftToApex.codIdx, q.2.leftToApex⟩ : StageRecord) :=
    stageRecord_computableIn
      (ComputableIn.comp (α := (RunState × ℕ) × AmalgamationDiagramData)
        (β := PotentialEmbeddingData) (σ := ℕ) (f := PotentialEmbeddingData.codIdx)
        (g := fun q ↦ q.2.leftToApex) PotentialEmbeddingData.codIdx_computable hleft)
      hleft
  have hl : ComputableIn E fun q : (RunState × ℕ) × AmalgamationDiagramData ↦
      q.1.1.stages ++ [(⟨q.2.leftToApex.codIdx, q.2.leftToApex⟩ : StageRecord)] :=
    ComputableIn₂.comp (α := (RunState × ℕ) × AmalgamationDiagramData) (β := List StageRecord)
      (γ := StageRecord) (σ := List StageRecord) (f := fun l a ↦ l ++ [a])
      (g := fun q ↦ q.1.1.stages) (h := fun q ↦ ⟨q.2.leftToApex.codIdx, q.2.leftToApex⟩)
      (Computable.list_concat.computableIn₂ (O := E))
      (ComputableIn.comp (α := (RunState × ℕ) × AmalgamationDiagramData) (β := RunState)
        (σ := List StageRecord) (f := RunState.stages) (g := fun q ↦ q.1.1) stages_computableIn
        (ComputableIn.fst.comp ComputableIn.fst))
      hrec
  have hr : ComputableIn E fun q : (RunState × ℕ) × AmalgamationDiagramData ↦
      q.1.1.fired ++ [q.1.2] :=
    ComputableIn₂.comp (α := (RunState × ℕ) × AmalgamationDiagramData) (β := List ℕ) (γ := ℕ)
      (σ := List ℕ) (f := fun l a ↦ l ++ [a]) (g := fun q ↦ q.1.1.fired) (h := fun q ↦ q.1.2)
      (Computable.list_concat.computableIn₂ (O := E))
      (ComputableIn.comp (α := (RunState × ℕ) × AmalgamationDiagramData) (β := RunState)
        (σ := List ℕ) (f := RunState.fired) (g := fun q ↦ q.1.1) fired_computableIn
        (ComputableIn.fst.comp ComputableIn.fst))
      (ComputableIn.snd.comp ComputableIn.fst)
  exact runState_computableIn hl hr

/-- The input of the innermost stage of the firing step. -/
private abbrev FireIn₃ : Type :=
  ((((RunState × ℕ) × ℕ) × RequirementData) × PotentialEmbeddingData) × PotentialEmbeddingData

/-- The input of the middle stage of the firing step. -/
private abbrev FireIn₂ : Type :=
  (((RunState × ℕ) × ℕ) × RequirementData) × PotentialEmbeddingData

/-- The input of the outer stage of the firing step. -/
private abbrev FireIn₁ : Type := ((RunState × ℕ) × ℕ) × RequirementData

private theorem fire_q₃ : ComputableIn E fun z : FireIn₃ ↦ z.1.1.2 :=
  ComputableIn.snd.comp (ComputableIn.fst.comp ComputableIn.fst)

/-- The coded extension map, as a function of the datum alone. -/
private theorem targetMap_computableIn : ComputableIn E RequirementData.targetMap :=
  (ofTriple_computableIn' (a := RequirementData.memberIdx) (b := RequirementData.targetIdx)
    (t := RequirementData.targetImage)
    (RequirementData.primrec_memberIdx.to_comp.computableIn (O := E))
    (RequirementData.primrec_targetIdx.to_comp.computableIn (O := E))
    (RequirementData.primrec_targetImage.to_comp.computableIn (O := E))).of_eq fun _ ↦ rfl

private theorem fire_targetMap : ComputableIn E fun z : FireIn₃ ↦ z.1.1.2.targetMap :=
  ComputableIn.comp (α := FireIn₃) (β := RequirementData) (σ := PotentialEmbeddingData)
    (f := RequirementData.targetMap) (g := fun z ↦ z.1.1.2) targetMap_computableIn fire_q₃

private theorem fire_span : ComputableIn E fun z : FireIn₃ ↦
    PotentialSpanData.ofPair (z.2, z.1.1.2.targetMap) :=
  ComputableIn.encode_iff.1
    ((ComputableIn.encode.comp (ComputableIn.pair (α := FireIn₃) (β := PotentialEmbeddingData)
      (γ := PotentialEmbeddingData) (f := fun z ↦ z.2) (g := fun z ↦ z.1.1.2.targetMap)
      ComputableIn.snd fire_targetMap)).of_eq fun _ ↦ rfl)

private theorem fire_sel : RecursiveIn E fun z : FireIn₃ ↦
    W.sel (PotentialSpanData.ofPair (z.2, z.1.1.2.targetMap)) :=
  RecursiveIn.comp (α := FireIn₃) (β := PotentialSpanData) (σ := AmalgamationDiagramData)
    (f := W.sel) (g := fun z ↦ PotentialSpanData.ofPair (z.2, z.1.1.2.targetMap))
    W.recursiveIn fire_span

private theorem fire_state : ComputableIn E fun y : FireIn₃ × AmalgamationDiagramData ↦
    y.1.1.1.1.1.1 :=
  ComputableIn.fst.comp (ComputableIn.fst.comp (ComputableIn.fst.comp
    (ComputableIn.fst.comp (ComputableIn.fst.comp ComputableIn.fst))))

private theorem fire_code : ComputableIn E fun y : FireIn₃ × AmalgamationDiagramData ↦
    y.1.1.1.1.2 :=
  ComputableIn.snd.comp (ComputableIn.fst.comp (ComputableIn.fst.comp
    (ComputableIn.fst.comp ComputableIn.fst)))

private theorem fire_ext : ComputableIn E fun y : FireIn₃ × AmalgamationDiagramData ↦
    y.1.1.1.1.1.1.capExtension y.1.1.1.1.2 y.2 :=
  ComputableIn.comp (α := FireIn₃ × AmalgamationDiagramData)
    (β := (RunState × ℕ) × AmalgamationDiagramData) (σ := RunState)
    (f := fun q ↦ q.1.1.capExtension q.1.2 q.2)
    (g := fun y ↦ ((y.1.1.1.1.1.1, y.1.1.1.1.2), y.2)) capExtension_computableIn
    (ComputableIn.pair (α := FireIn₃ × AmalgamationDiagramData) (β := RunState × ℕ)
      (γ := AmalgamationDiagramData) (f := fun y ↦ (y.1.1.1.1.1.1, y.1.1.1.1.2))
      (g := fun y ↦ y.2)
      (ComputableIn.pair (α := FireIn₃ × AmalgamationDiagramData) (β := RunState) (γ := ℕ)
        (f := fun y ↦ y.1.1.1.1.1.1) (g := fun y ↦ y.1.1.1.1.2) fire_state fire_code)
      ComputableIn.snd)

private theorem fire_q₂ : ComputableIn E fun y : FireIn₂ ↦ y.1.2 :=
  ComputableIn.snd.comp ComputableIn.fst

/-- The coded chain map, as a function of the state and the datum. -/
private theorem chainMap_computableIn :
    ComputableIn E fun p : RunState × RequirementData ↦ p.2.chainMap p.1.dHist :=
  (ofTriple_computableIn' (a := fun p ↦ p.2.memberIdx) (b := fun p ↦ p.1.dHist p.2.chainStage)
    (t := fun p ↦ p.2.chainImage)
    (ComputableIn.comp (α := RunState × RequirementData) (β := RequirementData) (σ := ℕ)
      (f := RequirementData.memberIdx) (g := fun p ↦ p.2)
      (RequirementData.primrec_memberIdx.to_comp.computableIn (O := E)) ComputableIn.snd)
    (ComputableIn.comp (α := RunState × RequirementData) (β := RunState × ℕ) (σ := ℕ)
      (f := fun p ↦ p.1.dHist p.2) (g := fun p ↦ (p.1, p.2.chainStage)) dHist_computableIn
      (ComputableIn.pair (α := RunState × RequirementData) (β := RunState) (γ := ℕ)
        (f := fun p ↦ p.1) (g := fun p ↦ p.2.chainStage) ComputableIn.fst
        (ComputableIn.comp (α := RunState × RequirementData) (β := RequirementData) (σ := ℕ)
          (f := RequirementData.chainStage) (g := fun p ↦ p.2)
          (RequirementData.primrec_chainStage.to_comp.computableIn (O := E)) ComputableIn.snd)))
    (ComputableIn.comp (α := RunState × RequirementData) (β := RequirementData) (σ := Tuple ℕ)
      (f := RequirementData.chainImage) (g := fun p ↦ p.2)
      (RequirementData.primrec_chainImage.to_comp.computableIn (O := E)) ComputableIn.snd)).of_eq
    fun _ ↦ rfl

private theorem fire_chainMap :
    ComputableIn E fun y : FireIn₂ ↦ y.1.2.chainMap y.1.1.1.1.dHist :=
  ComputableIn.comp (α := FireIn₂) (β := RunState × RequirementData)
    (σ := PotentialEmbeddingData) (f := fun p ↦ p.2.chainMap p.1.dHist)
    (g := fun y ↦ (y.1.1.1.1, y.1.2)) chainMap_computableIn
    (ComputableIn.pair (α := FireIn₂) (β := RunState) (γ := RequirementData)
      (f := fun y ↦ y.1.1.1.1) (g := fun y ↦ y.1.2)
      (ComputableIn.fst.comp (ComputableIn.fst.comp (ComputableIn.fst.comp ComputableIn.fst)))
      fire_q₂)

private theorem fire_comp (hOE : O ⊆ E) : RecursiveIn E fun y : FireIn₂ ↦
    K.compPart y.2 (y.1.2.chainMap y.1.1.1.1.dHist) :=
  RecursiveIn.comp (α := FireIn₂) (β := PotentialEmbeddingData × PotentialEmbeddingData)
    (σ := PotentialEmbeddingData) (f := fun p ↦ K.compPart p.1 p.2)
    (g := fun y ↦ (y.2, y.1.2.chainMap y.1.1.1.1.dHist))
    (RecursiveIn.mono hOE K.compPart_recursiveIn)
    (ComputableIn.pair (α := FireIn₂) (β := PotentialEmbeddingData) (γ := PotentialEmbeddingData)
      (f := fun y ↦ y.2) (g := fun y ↦ y.1.2.chainMap y.1.1.1.1.dHist) ComputableIn.snd
      fire_chainMap)

private theorem fire_trans (hOE : O ⊆ E) : RecursiveIn E fun w : FireIn₁ ↦
    K.transportPart w.1.1.1.stages w.2.chainStage w.1.1.2 :=
  RecursiveIn.comp (α := FireIn₁) (β := (List StageRecord × ℕ) × ℕ) (σ := PotentialEmbeddingData)
    (f := fun p ↦ K.transportPart p.1.1 p.1.2 p.2)
    (g := fun w ↦ ((w.1.1.1.stages, w.2.chainStage), w.1.1.2)) (K.transportPart_recursiveIn hOE)
    (ComputableIn.pair (α := FireIn₁) (β := List StageRecord × ℕ) (γ := ℕ)
      (f := fun w ↦ (w.1.1.1.stages, w.2.chainStage)) (g := fun w ↦ w.1.1.2)
      (ComputableIn.pair (α := FireIn₁) (β := List StageRecord) (γ := ℕ)
        (f := fun w ↦ w.1.1.1.stages) (g := fun w ↦ w.2.chainStage)
        (ComputableIn.comp (α := FireIn₁) (β := RunState) (σ := List StageRecord)
          (f := RunState.stages) (g := fun w ↦ w.1.1.1) stages_computableIn
          (ComputableIn.fst.comp (ComputableIn.fst.comp ComputableIn.fst)))
        (ComputableIn.comp (α := FireIn₁) (β := RequirementData) (σ := ℕ)
          (f := RequirementData.chainStage) (g := fun w ↦ w.2)
          (RequirementData.primrec_chainStage.to_comp.computableIn (O := E)) ComputableIn.snd))
      (ComputableIn.snd.comp (ComputableIn.fst.comp ComputableIn.fst)))

private theorem fire_dec : RecursiveIn E fun x : (RunState × ℕ) × ℕ ↦
    ((decode x.2 : Option RequirementData) : Part RequirementData) :=
  ComputableIn.ofOption (ComputableIn.comp (α := (RunState × ℕ) × ℕ) (β := ℕ)
    (σ := Option RequirementData) (f := decode) (g := fun x ↦ x.2)
    (Computable.decode.computableIn (O := E)) ComputableIn.snd)

private theorem fire_h₃ : RecursiveIn E fun z : FireIn₃ ↦
    (W.sel (PotentialSpanData.ofPair (z.2, z.1.1.2.targetMap))).map fun D ↦
      z.1.1.1.1.1.capExtension z.1.1.1.2 D :=
  RecursiveIn.map (fire_sel W) fire_ext.to₂

private theorem fire_h₂ (hOE : O ⊆ E) : RecursiveIn E fun y : FireIn₂ ↦
    (K.compPart y.2 (y.1.2.chainMap y.1.1.1.1.dHist)).bind fun F ↦
      (W.sel (PotentialSpanData.ofPair (F, y.1.2.targetMap))).map fun D ↦
        y.1.1.1.1.capExtension y.1.1.2 D :=
  RecursiveIn.bind (fire_comp hOE) (fire_h₃ W).to₂

private theorem fire_h₁ (hOE : O ⊆ E) : RecursiveIn E fun w : FireIn₁ ↦
    (K.transportPart w.1.1.1.stages w.2.chainStage w.1.1.2).bind fun δ ↦
      (K.compPart δ (w.2.chainMap w.1.1.1.dHist)).bind fun F ↦
        (W.sel (PotentialSpanData.ofPair (F, w.2.targetMap))).map fun D ↦
          w.1.1.1.capExtension w.1.2 D :=
  RecursiveIn.bind (fire_trans hOE) (fire_h₂ W hOE).to₂

private theorem firePart_recursiveIn (hOE : O ⊆ E) :
    RecursiveIn E fun x : (RunState × ℕ) × ℕ ↦ firePart K W x.1.1 x.1.2 x.2 :=
  (RecursiveIn.bind fire_dec (fire_h₁ W hOE).to₂).of_eq fun _ ↦ rfl

/-- **The transition is partial recursive** in the state and the clock stage, at any oracle reading
the family and running the selector. -/
theorem stepPart_recursiveIn (hOE : O ⊆ E) :
    RecursiveIn E fun p : RunState × ℕ ↦ stepPart K W p.1 p.2 :=
  (RecursiveIn.option_casesOn_right (α := RunState × ℕ) (β := ℕ) (σ := RunState)
    (o := fun p ↦ K.pickFromHistory (stageHistory p.1.stages) p.1.fired p.2)
    (f := fun p ↦ identityExtension K p.1 p.2) (g := fun p e ↦ firePart K W p.1 p.2 e)
    (pick_computableIn hOE) (identityExtension_computableIn hOE)
    (firePart_recursiveIn (W := W) hOE)).of_eq fun _ ↦ rfl

end Effectivity

/-! `firePart` and `stepPart` are sealed: unfolding `firePart` exposes `decode e` on a free code. -/
attribute [irreducible] firePart stepPart

theorem fired_identityExtension (S : RunState) (s : ℕ) :
    (identityExtension K S s).fired = S.fired := rfl

theorem stages_identityExtension (S : RunState) (s : ℕ) :
    (identityExtension K S s).stages =
      S.stages ++ [⟨S.currentMember s, K.idData (S.currentMember s)⟩] := rfl

/-! ### What a selection supplies -/

variable {K}

/-- **The payload of a selection**, read through the history: the selected code decodes to a datum
whose chain stage has been reached, whose static guards hold, and whose two coded maps are
carrier-valid — with `f` landing in the member recorded at stage `r`. No actualness. -/
theorem exists_decode_of_pick {S : RunState} {s e : ℕ}
    (hp : K.pickFromHistory (stageHistory S.stages) S.fired s = some e) :
    ∃ q : RequirementData, (decode e : Option RequirementData) = some q ∧
      q.chainStage ≤ s ∧ K.StaticAdmissible q ∧
        K.CarrierValid (q.chainMap S.dHist) ∧ K.CarrierValid q.targetMap := by
  obtain ⟨havail, -, -⟩ := K.avail_of_pickFromHistory hp
  obtain ⟨q, hq, hr, hstat⟩ := K.requirementAvail_sound S.dHist havail
  exact ⟨q, K.decode_eq_of_decodeAt _ hq, hr, hstat, K.decodeAt_carrierValid _ hq⟩

/-- Under the invariant, the transport from the decoded chain stage to the current stage halts on an
actual embedding from the member recorded at `r` to the current member. -/
theorem RunInvariant.exists_transport {S : RunState} {s : ℕ} (h : K.RunInvariant S s) {r : ℕ}
    (hr : r ≤ s) :
    ∃ δ ∈ K.transportPart S.stages r s,
      δ.domIdx = S.dHist r ∧ δ.codIdx = S.currentMember s ∧ K.PartialIsEmbedding δ := by
  obtain ⟨rr, hrr⟩ := h.exists_getElem? hr
  obtain ⟨rs, hrs⟩ := h.exists_getElem? (le_refl s)
  obtain ⟨δ, hδ, hdom, hcod, hemb⟩ := K.transportPart_partialIsEmbedding h.chain hr hrr hrs
  refine ⟨δ, hδ, ?_, ?_, hemb⟩
  · rw [hdom, h.dHist_eq hrr]
  · rw [hcod, RunState.currentMember, h.dHist_eq hrs]

/-! ### Halting -/

/-- **Halting from carrier validity and actual transport.** The scheduled candidate is only known
to be carrier-valid; the transport is actual by the invariant; composition lands carrier-valid data
by `compPart_carrierValid`, and the selector's halting clause finishes. -/
theorem stepPart_dom {S : RunState} {s : ℕ} (h : K.RunInvariant S s) : (stepPart K W S s).Dom := by
  rw [Part.dom_iff_mem]
  rcases hp : K.pickFromHistory (stageHistory S.stages) S.fired s with _ | e
  · exact ⟨_, (mem_stepPart_iff K W).2 (Or.inl ⟨hp, rfl⟩)⟩
  · obtain ⟨q, hq, hr, -, hf, hg⟩ := exists_decode_of_pick hp
    obtain ⟨δ, hδ, hdom, -, hemb⟩ := h.exists_transport hr
    have hFG : (q.chainMap S.dHist).codIdx = δ.domIdx := by rw [hdom]; rfl
    obtain ⟨F, hF, -, -, hFv⟩ := K.compPart_carrierValid hFG hf hemb
    have hspan : K.CarrierValidSpan (PotentialSpanData.ofPair (F, q.targetMap)) := ⟨hFv, hg⟩
    obtain ⟨D, hD⟩ := Part.dom_iff_mem.1 (W.halts _ hspan)
    exact ⟨_, (mem_stepPart_iff K W).2 (Or.inr ⟨e, hp, q, hq, δ, hδ, F, hF, D, hD, rfl⟩)⟩

/-! ### Invariant preservation -/

/-- **Invariant preservation, from the selector's unconditional clauses.** On the silent step the
identity data extends the chain; on a firing step the returned left leg is an actual embedding out
of the current member (well-shapedness) into the apex. No actualness of the candidate enters. -/
theorem runInvariant_of_mem {S : RunState} {s : ℕ} (h : K.RunInvariant S s) {S' : RunState}
    (hS' : S' ∈ stepPart K W S s) : K.RunInvariant S' (s + 1) := by
  obtain ⟨rs, hrs⟩ := h.exists_getElem? (le_refl s)
  have hlast : ∀ r ∈ S.stages.getLast?, r = rs := by
    intro r hr
    rw [h.getLast?_eq, hrs] at hr
    exact (Option.some.inj (Option.mem_def.1 hr)).symm
  have hcur : S.currentMember s = rs.memberIdx := by
    rw [RunState.currentMember, h.dHist_eq hrs]
  rcases (mem_stepPart_iff K W).1 hS' with ⟨-, rfl⟩ | ⟨e, hp, q, hq, δ, hδ, F, hF, D, hD, rfl⟩
  · refine ⟨h.chain.snoc (fun r hr ↦ ?_) rfl (K.idData_partialIsEmbedding _), ?_⟩
    · rw [hlast r hr, K.idData_domIdx, hcur]
    · rw [stages_identityExtension, List.length_append, h.length]; rfl
  · obtain ⟨hshape, hleft, -⟩ := W.unconditional _ D hD
    obtain ⟨q', hq', hr, -, -, -⟩ := exists_decode_of_pick hp
    rw [hq] at hq'
    obtain rfl := Option.some.inj hq'
    obtain ⟨δ', hδ', -, hcod', -⟩ := h.exists_transport hr
    obtain rfl := Part.mem_unique hδ hδ'
    obtain ⟨v, -, rfl⟩ := (K.mem_compPart_iff).1 hF
    refine ⟨h.chain.snoc (fun r hr' ↦ ?_) rfl hleft, ?_⟩
    · rw [hlast r hr', hshape.1, PotentialSpanData.ofPair_left]
      change δ.codIdx = rs.memberIdx
      rw [hcod', hcur]
    · rw [RunState.stages_capExtension, List.length_append, h.length]; rfl

/-! ### Requirement satisfaction -/

/-- **Requirement satisfaction, from actual inputs and the selector's conditional soundness.** When
the selected code's decoded maps are actual embeddings, the transported span is actual, so the
selector's right leg is actual and the square commutes. The stored record is the left leg; the right
leg is recovered here through the membership specification. -/
theorem exists_square_of_fire {S : RunState} {s e : ℕ} (h : K.RunInvariant S s)
    (hp : K.pickFromHistory (stageHistory S.stages) S.fired s = some e) {q : RequirementData}
    (hq : (decode e : Option RequirementData) = some q)
    (hf : K.PartialIsEmbedding (q.chainMap S.dHist)) (hg : K.PartialIsEmbedding q.targetMap) :
    ∃ δ ∈ K.transportPart S.stages q.chainStage s,
      ∃ F ∈ K.compPart δ (q.chainMap S.dHist),
        ∃ D ∈ W.sel (PotentialSpanData.ofPair (F, q.targetMap)),
          K.PartialIsEmbedding F ∧ K.PartialIsEmbedding D.rightToApex ∧
            K.PartialCommutes (PotentialSpanData.ofPair (F, q.targetMap)) D ∧
              S.capExtension e D ∈ stepPart K W S s := by
  obtain ⟨q', hq', hr, -, -, -⟩ := exists_decode_of_pick hp
  rw [hq] at hq'
  obtain rfl := Option.some.inj hq'
  obtain ⟨δ, hδ, hdom, -, hemb⟩ := h.exists_transport hr
  have hFG : (q.chainMap S.dHist).codIdx = δ.domIdx := by rw [hdom]; rfl
  obtain ⟨F, hF, hFdom, -, hFemb⟩ := K.compPart_partialIsEmbedding hFG hf hemb
  have hspan : K.PartialSpanActual (PotentialSpanData.ofPair (F, q.targetMap)) :=
    ⟨by rw [PotentialSpanData.WellShaped, PotentialSpanData.ofPair_left,
        PotentialSpanData.ofPair_right, hFdom]; rfl, hFemb, hg⟩
  obtain ⟨D, hD⟩ := Part.dom_iff_mem.1 (W.halts _ hspan.carrierValidSpan)
  obtain ⟨hright, hcomm⟩ := W.sound _ D hD hspan
  exact ⟨δ, hδ, F, hF, D, hD, hFemb, hright, hcomm,
    (mem_stepPart_iff K W).2 (Or.inr ⟨e, hp, q, hq, δ, hδ, F, hF, D, hD, rfl⟩)⟩

end PartialAgeIn

end FirstOrder.Language
