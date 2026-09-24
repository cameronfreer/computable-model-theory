/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.ExtensionBridge
import ComputableModelTheory.ModelTheory.Computable.CeStructureOmegaTuple
import ComputableModelTheory.ModelTheory.Computable.ComputablyHomogeneous
import ComputableModelTheory.ModelTheory.Computable.PartialSelectorSpecs

/-!
# The homogeneity selector of Theorem 3.9's construction

The ω structure `F := Z.omegaStructure cert` of the run's limit is computably homogeneous
(CHMM Definition 3.1). The selector is a program: a `Part`-valued pipeline, totalized once.

0. **Length mismatch.** When `d⃗` and `c⃗ = g(d⃗)` have different lengths the answer is
   `γ := d⃗ ++ [x]`, `y := x`. No embedding realizes such a `g`, so only the unconditional clauses
   bind, and they hold.
1. **Common stage.** `rankTupleAtStagePart` pulls `d⃗ ++ c⃗ ++ [x]` back to one stage `r`, together
   with the stage tuple `u` — a program, not a stage chosen from exhaustion.
2. **Represent by CHP**, at the *member index* `memberIdx r`: `a` from `u.take n` and `k` from
   `u.drop n`. The requirement is `⟨a, r, k, u.take n, (K.gens k).take n⟩`. Its second tuple is
   positional, so the requirement is admissible whether or not `g` is actual — which is what makes
   the search below halt on malformed input.
3. **Firing search.** The least `s` at which the run's history selects the requirement's encoding:
   `Nat.rfind` over the computable firing test. It halts by fairness.
4. **The CAP payload** is recomputed at `s` exactly as the run's transition computes it — the
   transport, the transported chain map, and the CAP selector on the span — rather than read off
   `exists_capExtension_of_firesAt`, which identifies what the run did but is not a program.
5. **Answer.** `γ` is the apex member's own recorded generators, carried into ω by the recoded stage
   map at `s + 1`; `y` is the last coordinate of the diagram's right range tuple, carried the same
   way. The left leg's range tuple would be wrong: it names the images of the old stage's
   generators, need not generate the apex, and need not contain `y` in its closure.

The unconditional clauses use only well-formedness of the right leg (`PartialWellFormed`, from the
selector's unconditional clause) and that every stage element maps into the apex's image. The
conditional clause is the only place the square is used.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-! ### Positional bookkeeping and canonical members as ranges -/

theorem _root_.List.Forall₂.exists_getElem?_right {α β : Type*} {R : α → β → Prop}
    {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂) {j : ℕ} {a : α}
    (ha : l₁[j]? = Option.some a) : ∃ b, l₂[j]? = Option.some b ∧ R a b := by
  induction h generalizing j with
  | nil => simp at ha
  | @cons a' b' _ _ hab _ ih =>
    cases j with
    | zero =>
      obtain rfl : a' = a := by simpa using ha
      exact ⟨b', rfl, hab⟩
    | succ j => simpa using ih (by simpa using ha)

theorem _root_.List.Forall₂.exists_getElem?_left {α β : Type*} {R : α → β → Prop}
    {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂) {j : ℕ} {b : β}
    (hb : l₂[j]? = Option.some b) : ∃ a, l₁[j]? = Option.some a ∧ R a b := by
  induction h generalizing j with
  | nil => simp at hb
  | @cons a' b' _ _ hab _ ih =>
    cases j with
    | zero =>
      obtain rfl : b' = b := by simpa using hb
      exact ⟨a', rfl, hab⟩
    | succ j => simpa using ih (by simpa using hb)

/-- A tuple whose entries are, position by position, the values of `v` has `v`'s range. -/
theorem range_view_eq_of_getElem? {t : List ℕ} {n : ℕ} {v : Fin n → ℕ} (hlen : t.length = n)
    (h : ∀ k : Fin n, t[(k : ℕ)]? = Option.some (v k)) :
    Set.range (Tuple.view t) = Set.range v := by
  ext y
  simp only [Set.mem_range, Tuple.view_eq_get]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨Fin.cast hlen k, ?_⟩
    have := h (Fin.cast hlen k)
    rw [Fin.val_cast, List.getElem?_eq_getElem k.2] at this
    exact (Option.some.inj this).symm
  · rintro ⟨k, rfl⟩
    have hk : (k : ℕ) < t.length := hlen ▸ k.2
    refine ⟨⟨k, hk⟩, ?_⟩
    have := h k
    rw [List.getElem?_eq_getElem hk] at this
    exact Option.some.inj this

namespace PartialCePresentationIn

variable {E' : Set (ℕ →. ℕ)}

/-- An embedding into the ambient structure that lands in the carrier, as an embedding into the
carrier. -/
def codRestrict (P : PartialCePresentationIn E' L) {M : Type*} [L.Structure M]
    (e : @Language.Embedding L M ℕ _ P.str) (h : ∀ x, e x ∈ P.domain) : M ↪[L] P.domain :=
  letI : L.Structure ℕ := P.str
  { toFun := fun x ↦ ⟨e x, h x⟩
    inj' := fun _ _ hxy ↦ e.injective (congrArg Subtype.val hxy)
    map_fun' := fun f v ↦ Subtype.ext (e.map_fun f v)
    map_rel' := fun r v ↦ e.map_rel r v }

@[simp] theorem codRestrict_coe (P : PartialCePresentationIn E' L) {M : Type*} [L.Structure M]
    (e : @Language.Embedding L M ℕ _ P.str) (h : ∀ x, e x ∈ P.domain) (x : M) :
    ((P.codRestrict e h x : P.domain) : ℕ) = e x :=
  rfl

end PartialCePresentationIn

/-- **A canonical member is the range of any embedding carrying some member's recorded generators
onto its tuple**: the member is generated by its generators, and embeddings carry closures to
closures. -/
theorem ComputableStructureIn.canonicalAge_domainAt_eq_range {E' : Set (ℕ →. ℕ)}
    (S : ComputableStructureIn E L) {A : PartialAgeIn E' L} {c : ℕ}
    (e : @Language.Embedding L (A.memberAt c).domain ℕ _ S.inst) {t : Tuple ℕ}
    (ht : Set.range (Tuple.view t) = Set.range fun k ↦ e (A.gensView c k)) :
    S.canonicalAge.domainAt (encode t) = Set.range e := by
  letI : L.Structure ℕ := S.inst
  rw [S.canonicalAge_domainAt_eq_closure, allTupleFor_encode, ht]
  ext y
  rw [SetLike.mem_coe, mem_closure_range_iff_exists_term]
  constructor
  · rintro ⟨T, rfl⟩
    exact ⟨T.realize (A.gensView c), (HomClass.realize_term e (t := T) (v := A.gensView c)).symm⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨T, rfl⟩ := PartialAgeIn.exists_realize_gensView x
    exact ⟨T, HomClass.realize_term e (t := T) (v := A.gensView c)⟩

namespace PartialAgeIn

/-! ### The pipeline -/

section Pipeline

variable (K : PartialAgeIn O L) (W : PartialCAPWitness E K) (i : ℕ)

/-- **The firing test**: at clock `s`, the run's history selects the code `e`. -/
noncomputable def firesTest (e s : ℕ) : Bool :=
  decide
    (K.pickFromHistory (stageHistory (run K W i s).stages) (run K W i s).fired s = Option.some e)

/-- **The firing search**: the least clock at which the run selects `e`. -/
noncomputable def firingSearch (e : ℕ) : Part ℕ :=
  Nat.rfind fun s ↦ Part.some (firesTest K W i e s)

/-- **The CAP payload** of requirement `q` at clock `s`, computed as the run's transition computes
it: the transport, the transported chain map, and the selector on the span. -/
noncomputable def payloadPart (s : ℕ) (q : RequirementData) : Part AmalgamationDiagramData :=
  (K.transportPart (run K W i s).stages q.chainStage s).bind fun δ ↦
    (K.compPart δ (q.chainMap (run K W i s).dHist)).bind fun F ↦
      W.sel (PotentialSpanData.ofPair (F, q.targetMap))

variable {K W i} {hOE : O ⊆ E} {h0 : (K.domainAt i).Nonempty}
variable (Z : (runChain K W i hOE h0).LimitIn)

/-- **The answer** from a firing at clock `s` with diagram `D`: the apex member's recorded
generators in ω, and the last coordinate of the right range tuple in ω. -/
noncomputable def answerPart (s : ℕ) (D : AmalgamationDiagramData) : Part HomogeneityAnswerData :=
  (listMapPart (Z.rankStageMap (s + 1)) (K.gens (memberIdx K W i (s + 1)))).bind fun γ ↦
    (Z.rankStageMap (s + 1) (D.rightToApex.rangeTuple.getLastD 0)).map fun y ↦ ⟨γ, y⟩

/-- Search for the requirement's firing, recompute its payload, and answer. -/
noncomputable def fromRequirementPart (q : RequirementData) : Part HomogeneityAnswerData :=
  (firingSearch K W i (encode q)).bind fun s ↦
    (payloadPart K W i s q).bind fun D ↦ answerPart Z s D

/-- The query's three pieces, as one tuple of ω-codes. -/
def _root_.FirstOrder.Language.HomogeneityQueryData.fullTuple (q : HomogeneityQueryData) : List ℕ :=
  q.domainTuple ++ q.imageTuple ++ [q.newPoint]

variable (K) in
/-- The requirement formed from a query of width `n` pulled back to `p = (r, u)`, with `a`
representing `u.take n` and `k` representing `u.drop n`. The second tuple is positional: the first
`n` recorded generators of `A_k`. -/
def queryRequirement (n : ℕ) (p : ℕ × List ℕ) (a k : ℕ) : RequirementData :=
  ⟨a, p.1, k, p.2.take n, (K.gens k).take n⟩

variable (chpSel : ℕ → List ℕ →. ℕ)

/-- **The requirement of a query**: pull the full tuple back to a common stage, then represent
`d⃗` and `c⃗ ++ [x]` by CHP at the stage's member index. -/
noncomputable def requirementPart (q : HomogeneityQueryData) : Part RequirementData :=
  (Z.rankTupleAtStagePart q.fullTuple).bind fun p ↦
    (chpSel (memberIdx K W i p.1) (p.2.take q.domainTuple.length)).bind fun a ↦
      (chpSel (memberIdx K W i p.1) (p.2.drop q.domainTuple.length)).map fun k ↦
        queryRequirement K q.domainTuple.length p a k

/-- The fallback answer on a length-mismatched query. -/
def fallbackAnswer (q : HomogeneityQueryData) : HomogeneityAnswerData :=
  ⟨q.domainTuple ++ [q.newPoint], q.newPoint⟩

/-- The query, when its two tuples have the same length. -/
def matchedQuery? (q : HomogeneityQueryData) : Option HomogeneityQueryData :=
  if q.domainTuple.length = q.imageTuple.length then some q else none

/-- **The selector, as a program.** -/
noncomputable def selectPart (q : HomogeneityQueryData) : Part HomogeneityAnswerData :=
  Option.casesOn (motive := fun _ ↦ Part HomogeneityAnswerData) (matchedQuery? q)
    (Part.some (fallbackAnswer q))
    fun q' ↦ (requirementPart Z chpSel q').bind (fromRequirementPart Z)

end Pipeline

/-! ### Effectivity

Every combinator is pinned on its types: the run state and the requirement are `ofEquiv`-encoded
structures. -/

section Effectivity

variable {K : PartialAgeIn O L} {W : PartialCAPWitness E K} {i : ℕ}

private theorem run_stages_computableIn (hOE : O ⊆ E) :
    ComputableIn E fun s ↦ (run K W i s).stages :=
  ComputableIn.comp (α := ℕ) (β := RunState) (σ := List StageRecord) (f := RunState.stages)
    (g := run K W i) (RunState.primrec_stages.to_comp.computableIn (O := E)) (run_computableIn hOE)

private theorem run_pick_computableIn (hOE : O ⊆ E) : ComputableIn E fun s ↦
    K.pickFromHistory (stageHistory (run K W i s).stages) (run K W i s).fired s :=
  ComputableIn.comp (α := ℕ) (β := (List ℕ × List ℕ) × ℕ) (σ := Option ℕ)
    (f := fun x ↦ K.pickFromHistory x.1.1 x.1.2 x.2)
    (g := fun s ↦ ((stageHistory (run K W i s).stages, (run K W i s).fired), s))
    (K.pickFromHistory_computableIn hOE)
    (ComputableIn.pair (α := ℕ) (β := List ℕ × List ℕ) (γ := ℕ)
      (f := fun s ↦ (stageHistory (run K W i s).stages, (run K W i s).fired)) (g := fun s ↦ s)
      (ComputableIn.pair (α := ℕ) (β := List ℕ) (γ := List ℕ)
        (f := fun s ↦ stageHistory (run K W i s).stages) (g := fun s ↦ (run K W i s).fired)
        (ComputableIn.comp (α := ℕ) (β := List StageRecord) (σ := List ℕ) (f := stageHistory)
          (g := fun s ↦ (run K W i s).stages) stageHistory_computableIn
          (run_stages_computableIn hOE))
        (ComputableIn.comp (α := ℕ) (β := RunState) (σ := List ℕ) (f := RunState.fired)
          (g := run K W i) (RunState.primrec_fired.to_comp.computableIn (O := E))
          (run_computableIn hOE)))
      ComputableIn.id)

theorem firesTest_computableIn (hOE : O ⊆ E) :
    ComputableIn₂ E (firesTest K W i) :=
  ComputableIn₂.comp (α := ℕ × ℕ) (β := Option ℕ) (γ := Option ℕ) (σ := Bool)
    (f := fun a b ↦ decide (a = b))
    (g := fun p ↦ K.pickFromHistory (stageHistory (run K W i p.2).stages) (run K W i p.2).fired p.2)
    (h := fun p ↦ some p.1)
    ((Primrec.eq (α := Option ℕ)).decide.to_comp.computableIn₂ (O := E))
    (ComputableIn.comp (α := ℕ × ℕ) (β := ℕ) (σ := Option ℕ)
      (f := fun s ↦ K.pickFromHistory (stageHistory (run K W i s).stages) (run K W i s).fired s)
      (g := fun p ↦ p.2) (run_pick_computableIn hOE) ComputableIn.snd)
    (ComputableIn.comp (α := ℕ × ℕ) (β := ℕ) (σ := Option ℕ) (f := some) (g := fun p ↦ p.1)
      ComputableIn.option_some ComputableIn.fst)

theorem firingSearch_recursiveIn (hOE : O ⊆ E) : RecursiveIn E (firingSearch K W i) :=
  RecursiveIn.rfind_total (f := firesTest K W i) (firesTest_computableIn hOE)

/-- Potential embedding data from computable components, crossing the encoding. -/
private theorem ofTriple_computableIn {α : Type*} [Primcodable α] {a b : α → ℕ}
    {t : α → Tuple ℕ} (ha : ComputableIn E a) (hb : ComputableIn E b) (ht : ComputableIn E t) :
    ComputableIn E fun x ↦ PotentialEmbeddingData.ofTriple (a x, b x, t x) :=
  ComputableIn.comp (α := α) (β := ℕ × ℕ × Tuple ℕ) (σ := PotentialEmbeddingData)
    (f := PotentialEmbeddingData.ofTriple) (g := fun x ↦ (a x, b x, t x))
    (PotentialEmbeddingData.primrec_ofTriple.to_comp.computableIn (O := E))
    (ComputableIn.pair (α := α) (β := ℕ) (γ := ℕ × Tuple ℕ) (f := a) (g := fun x ↦ (b x, t x)) ha
      (ComputableIn.pair (α := α) (β := ℕ) (γ := Tuple ℕ) (f := b) (g := t) hb ht))

private theorem chainMap_run_computableIn (hOE : O ⊆ E) :
    ComputableIn E fun p : ℕ × RequirementData ↦ p.2.chainMap (run K W i p.1).dHist := by
  have hq : ComputableIn E fun p : ℕ × RequirementData ↦ p.2 := ComputableIn.snd
  have hhist : ComputableIn E fun p : ℕ × RequirementData ↦ stageHistory (run K W i p.1).stages :=
    ComputableIn.comp (α := ℕ × RequirementData) (β := ℕ) (σ := List ℕ)
      (f := fun s ↦ stageHistory (run K W i s).stages) (g := fun p ↦ p.1)
      (ComputableIn.comp (α := ℕ) (β := List StageRecord) (σ := List ℕ) (f := stageHistory)
        (g := fun s ↦ (run K W i s).stages) stageHistory_computableIn
        (run_stages_computableIn hOE))
      ComputableIn.fst
  have hstage : ComputableIn E fun p : ℕ × RequirementData ↦ p.2.chainStage :=
    ComputableIn.comp (α := ℕ × RequirementData) (β := RequirementData) (σ := ℕ)
      (f := RequirementData.chainStage) (g := fun p ↦ p.2)
      (RequirementData.primrec_chainStage.to_comp.computableIn (O := E)) hq
  have hd : ComputableIn E fun p : ℕ × RequirementData ↦ (run K W i p.1).dHist p.2.chainStage :=
    ComputableIn₂.comp (α := ℕ × RequirementData) (β := List ℕ) (γ := ℕ) (σ := ℕ)
      (f := fun l n ↦ l.getD n 0) (g := fun p ↦ stageHistory (run K W i p.1).stages)
      (h := fun p ↦ p.2.chainStage) ((Primrec.list_getD (0 : ℕ)).to_comp.computableIn₂ (O := E))
      hhist hstage
  exact (ofTriple_computableIn (a := fun p : ℕ × RequirementData ↦ p.2.memberIdx)
    (b := fun p ↦ (run K W i p.1).dHist p.2.chainStage) (t := fun p ↦ p.2.chainImage)
    (ComputableIn.comp (α := ℕ × RequirementData) (β := RequirementData) (σ := ℕ)
      (f := RequirementData.memberIdx) (g := fun p ↦ p.2)
      (RequirementData.primrec_memberIdx.to_comp.computableIn (O := E)) hq)
    hd
    (ComputableIn.comp (α := ℕ × RequirementData) (β := RequirementData) (σ := Tuple ℕ)
      (f := RequirementData.chainImage) (g := fun p ↦ p.2)
      (RequirementData.primrec_chainImage.to_comp.computableIn (O := E)) hq)).of_eq
    fun _ ↦ rfl

private theorem targetMap_computableIn' :
    ComputableIn E RequirementData.targetMap :=
  (ofTriple_computableIn (a := RequirementData.memberIdx) (b := RequirementData.targetIdx)
    (t := RequirementData.targetImage)
    (RequirementData.primrec_memberIdx.to_comp.computableIn (O := E))
    (RequirementData.primrec_targetIdx.to_comp.computableIn (O := E))
    (RequirementData.primrec_targetImage.to_comp.computableIn (O := E))).of_eq fun _ ↦ rfl

/-- The inner stage of the payload: the input with the transport. -/
private abbrev PayIn₁ : Type := (ℕ × RequirementData) × PotentialEmbeddingData

/-- The innermost stage of the payload: with the transported chain map too. -/
private abbrev PayIn₂ : Type := PayIn₁ × PotentialEmbeddingData

theorem payloadPart_recursiveIn (hOE : O ⊆ E) :
    RecursiveIn E fun p : ℕ × RequirementData ↦ payloadPart K W i p.1 p.2 := by
  have htrans : RecursiveIn E fun p : ℕ × RequirementData ↦
      K.transportPart (run K W i p.1).stages p.2.chainStage p.1 :=
    RecursiveIn.comp (α := ℕ × RequirementData) (β := (List StageRecord × ℕ) × ℕ)
      (σ := PotentialEmbeddingData) (f := fun x ↦ K.transportPart x.1.1 x.1.2 x.2)
      (g := fun p ↦ (((run K W i p.1).stages, p.2.chainStage), p.1))
      (K.transportPart_recursiveIn hOE)
      (ComputableIn.pair (α := ℕ × RequirementData) (β := List StageRecord × ℕ) (γ := ℕ)
        (f := fun p ↦ ((run K W i p.1).stages, p.2.chainStage)) (g := fun p ↦ p.1)
        (ComputableIn.pair (α := ℕ × RequirementData) (β := List StageRecord) (γ := ℕ)
          (f := fun p ↦ (run K W i p.1).stages) (g := fun p ↦ p.2.chainStage)
          (ComputableIn.comp (α := ℕ × RequirementData) (β := ℕ) (σ := List StageRecord)
            (f := fun s ↦ (run K W i s).stages) (g := fun p ↦ p.1) (run_stages_computableIn hOE)
            ComputableIn.fst)
          (ComputableIn.comp (α := ℕ × RequirementData) (β := RequirementData) (σ := ℕ)
            (f := RequirementData.chainStage) (g := fun p ↦ p.2)
            (RequirementData.primrec_chainStage.to_comp.computableIn (O := E)) ComputableIn.snd))
        ComputableIn.fst)
  have hcomp : RecursiveIn E fun y : PayIn₁ ↦
      K.compPart y.2 (y.1.2.chainMap (run K W i y.1.1).dHist) :=
    RecursiveIn.comp (α := PayIn₁) (β := PotentialEmbeddingData × PotentialEmbeddingData)
      (σ := PotentialEmbeddingData) (f := fun x ↦ K.compPart x.1 x.2)
      (g := fun y ↦ (y.2, y.1.2.chainMap (run K W i y.1.1).dHist))
      (RecursiveIn.mono hOE K.compPart_recursiveIn)
      (ComputableIn.pair (α := PayIn₁) (β := PotentialEmbeddingData)
        (γ := PotentialEmbeddingData) (f := fun y ↦ y.2)
        (g := fun y ↦ y.1.2.chainMap (run K W i y.1.1).dHist) ComputableIn.snd
        (ComputableIn.comp (α := PayIn₁) (β := ℕ × RequirementData) (σ := PotentialEmbeddingData)
          (f := fun p ↦ p.2.chainMap (run K W i p.1).dHist) (g := fun y ↦ y.1)
          (chainMap_run_computableIn hOE) ComputableIn.fst))
  have hspan : ComputableIn E fun z : PayIn₂ ↦
      PotentialSpanData.ofPair (z.2, z.1.1.2.targetMap) :=
    ComputableIn.comp (α := PayIn₂) (β := PotentialEmbeddingData × PotentialEmbeddingData)
      (σ := PotentialSpanData) (f := PotentialSpanData.ofPair)
      (g := fun z ↦ (z.2, z.1.1.2.targetMap)) PotentialSpanData.ofPair_computableIn
      (ComputableIn.pair (α := PayIn₂) (β := PotentialEmbeddingData)
        (γ := PotentialEmbeddingData) (f := fun z ↦ z.2) (g := fun z ↦ z.1.1.2.targetMap)
        ComputableIn.snd
        (ComputableIn.comp (α := PayIn₂) (β := RequirementData) (σ := PotentialEmbeddingData)
          (f := RequirementData.targetMap) (g := fun z ↦ z.1.1.2) targetMap_computableIn'
          (ComputableIn.snd.comp (ComputableIn.fst.comp ComputableIn.fst))))
  have hsel : RecursiveIn E fun z : PayIn₂ ↦
      W.sel (PotentialSpanData.ofPair (z.2, z.1.1.2.targetMap)) :=
    RecursiveIn.comp (α := PayIn₂) (β := PotentialSpanData) (σ := AmalgamationDiagramData)
      (f := W.sel) (g := fun z ↦ PotentialSpanData.ofPair (z.2, z.1.1.2.targetMap))
      W.recursiveIn hspan
  exact (RecursiveIn.bind htrans (RecursiveIn.bind hcomp hsel.to₂).to₂).of_eq fun _ ↦ rfl

end Effectivity

section EffectivityLimit

variable {K : PartialAgeIn O L} {W : PartialCAPWitness E K} {i : ℕ} {hOE : O ⊆ E}
  {h0 : (K.domainAt i).Nonempty} (Z : (runChain K W i hOE h0).LimitIn)

private theorem primrec_getLastD : Primrec fun l : List ℕ ↦ l.getLastD 0 :=
  (Primrec.option_getD.comp (Primrec.list_head?.comp Primrec.list_reverse)
    (Primrec.const 0)).of_eq fun l ↦ by
      rw [List.head?_reverse, List.getLastD_eq_getLast?]

/-- The answer stage's input: the clock and the diagram, with the computed `γ`. -/
private abbrev AnsIn : Type := (ℕ × AmalgamationDiagramData) × List ℕ

theorem answerPart_recursiveIn :
    RecursiveIn E fun p : ℕ × AmalgamationDiagramData ↦ answerPart Z p.1 p.2 := by
  have hsucc : ComputableIn E fun p : ℕ × AmalgamationDiagramData ↦ p.1 + 1 :=
    ComputableIn.comp (α := ℕ × AmalgamationDiagramData) (β := ℕ) (σ := ℕ) (f := Nat.succ)
      (g := fun p ↦ p.1) (Primrec.succ.to_comp.computableIn (O := E)) ComputableIn.fst
  have hgens : ComputableIn E fun p : ℕ × AmalgamationDiagramData ↦
      K.gens (memberIdx K W i (p.1 + 1)) :=
    ComputableIn.comp (α := ℕ × AmalgamationDiagramData) (β := ℕ) (σ := List ℕ) (f := K.gens)
      (g := fun p ↦ memberIdx K W i (p.1 + 1)) (RecursiveIn.mono hOE K.gens_computableIn)
      (ComputableIn.comp (α := ℕ × AmalgamationDiagramData) (β := ℕ) (σ := ℕ)
        (f := memberIdx K W i) (g := fun p ↦ p.1 + 1) (memberIdx_computableIn K W i hOE) hsucc)
  have hlist : RecursiveIn E fun p : ℕ × AmalgamationDiagramData ↦
      listMapPart (Z.rankStageMap (p.1 + 1)) (K.gens (memberIdx K W i (p.1 + 1))) :=
    RecursiveIn₂.comp (α := ℕ × AmalgamationDiagramData) (β := ℕ) (γ := List ℕ) (σ := List ℕ)
      (f := fun s l ↦ listMapPart (Z.rankStageMap s) l) (g := fun p ↦ p.1 + 1)
      (h := fun p ↦ K.gens (memberIdx K W i (p.1 + 1)))
      (RecursiveIn.listMapPart₂ (g := Z.rankStageMap) Z.rankStageMap_recursiveIn) hsucc hgens
  have hlast : ComputableIn E fun y : AnsIn ↦ y.1.2.rightToApex.rangeTuple.getLastD 0 :=
    ComputableIn.comp (α := AnsIn) (β := List ℕ) (σ := ℕ) (f := fun l ↦ l.getLastD 0)
      (g := fun y ↦ y.1.2.rightToApex.rangeTuple) (primrec_getLastD.to_comp.computableIn (O := E))
      (ComputableIn.comp (α := AnsIn) (β := PotentialEmbeddingData) (σ := List ℕ)
        (f := PotentialEmbeddingData.rangeTuple) (g := fun y ↦ y.1.2.rightToApex)
        (PotentialEmbeddingData.primrec_rangeTuple.to_comp.computableIn (O := E))
        (ComputableIn.comp (α := AnsIn) (β := AmalgamationDiagramData)
          (σ := PotentialEmbeddingData) (f := AmalgamationDiagramData.rightToApex)
          (g := fun y ↦ y.1.2) AmalgamationDiagramData.rightToApex_computable
          (ComputableIn.snd.comp ComputableIn.fst)))
  have hy : RecursiveIn E fun y : AnsIn ↦
      Z.rankStageMap (y.1.1 + 1) (y.1.2.rightToApex.rangeTuple.getLastD 0) :=
    RecursiveIn.comp (α := AnsIn) (β := ℕ × ℕ) (σ := ℕ) (f := fun x ↦ Z.rankStageMap x.1 x.2)
      (g := fun y ↦ (y.1.1 + 1, y.1.2.rightToApex.rangeTuple.getLastD 0))
      Z.rankStageMap_recursiveIn
      (ComputableIn.pair (α := AnsIn) (β := ℕ) (γ := ℕ) (f := fun y ↦ y.1.1 + 1)
        (g := fun y ↦ y.1.2.rightToApex.rangeTuple.getLastD 0)
        (ComputableIn.comp (α := AnsIn) (β := ℕ × AmalgamationDiagramData) (σ := ℕ)
          (f := fun p ↦ p.1 + 1) (g := fun y ↦ y.1) hsucc ComputableIn.fst)
        hlast)
  have hans : ComputableIn E fun w : AnsIn × ℕ ↦ (⟨w.1.2, w.2⟩ : HomogeneityAnswerData) :=
    ComputableIn.comp (α := AnsIn × ℕ) (β := Tuple ℕ × ℕ) (σ := HomogeneityAnswerData)
      (f := fun p ↦ ⟨p.1, p.2⟩) (g := fun w ↦ (w.1.2, w.2))
      (primrec_homogeneityAnswerData.to_comp.computableIn (O := E))
      (ComputableIn.pair (α := AnsIn × ℕ) (β := Tuple ℕ) (γ := ℕ) (f := fun w ↦ w.1.2)
        (g := fun w ↦ w.2) (ComputableIn.snd.comp ComputableIn.fst) ComputableIn.snd)
  exact (RecursiveIn.bind hlist (RecursiveIn.map hy hans.to₂).to₂).of_eq fun _ ↦ rfl

theorem fromRequirementPart_recursiveIn : RecursiveIn E (fromRequirementPart Z) := by
  have hsearch : RecursiveIn E fun q : RequirementData ↦ firingSearch K W i (encode q) :=
    RecursiveIn.comp (α := RequirementData) (β := ℕ) (σ := ℕ) (f := firingSearch K W i)
      (g := encode) (firingSearch_recursiveIn hOE) ComputableIn.encode
  have hpay : RecursiveIn E fun y : RequirementData × ℕ ↦ payloadPart K W i y.2 y.1 :=
    RecursiveIn.comp (α := RequirementData × ℕ) (β := ℕ × RequirementData)
      (σ := AmalgamationDiagramData) (f := fun p ↦ payloadPart K W i p.1 p.2)
      (g := fun y ↦ (y.2, y.1)) (payloadPart_recursiveIn hOE)
      (ComputableIn.pair (α := RequirementData × ℕ) (β := ℕ) (γ := RequirementData)
        (f := fun y ↦ y.2) (g := fun y ↦ y.1) ComputableIn.snd ComputableIn.fst)
  have hans : RecursiveIn E fun z : (RequirementData × ℕ) × AmalgamationDiagramData ↦
      answerPart Z z.1.2 z.2 :=
    RecursiveIn.comp (α := (RequirementData × ℕ) × AmalgamationDiagramData)
      (β := ℕ × AmalgamationDiagramData) (σ := HomogeneityAnswerData)
      (f := fun p ↦ answerPart Z p.1 p.2) (g := fun z ↦ (z.1.2, z.2)) (answerPart_recursiveIn Z)
      (ComputableIn.pair (α := (RequirementData × ℕ) × AmalgamationDiagramData) (β := ℕ)
        (γ := AmalgamationDiagramData) (f := fun z ↦ z.1.2) (g := fun z ↦ z.2)
        (ComputableIn.snd.comp ComputableIn.fst) ComputableIn.snd)
  exact (RecursiveIn.bind hsearch (RecursiveIn.bind hpay hans.to₂).to₂).of_eq fun _ ↦ rfl

theorem primrec_fullTuple : Primrec HomogeneityQueryData.fullTuple :=
  (Primrec.list_append.comp
    (Primrec.list_append.comp HomogeneityQueryData.primrec_domainTuple
      HomogeneityQueryData.primrec_imageTuple)
    (Primrec.list_cons.comp HomogeneityQueryData.primrec_newPoint (Primrec.const []))).of_eq
    fun _ ↦ rfl

/-- The requirement stage's inputs. -/
private abbrev ReqIn₁ : Type := HomogeneityQueryData × (ℕ × List ℕ)

private abbrev ReqIn₂ : Type := ReqIn₁ × ℕ

variable (chpSel : ℕ → List ℕ →. ℕ)

theorem requirementPart_recursiveIn
    (hchp : RecursiveIn E fun p : ℕ × List ℕ ↦ chpSel p.1 p.2) :
    RecursiveIn E (requirementPart Z chpSel) := by
  have hpull : RecursiveIn E fun q : HomogeneityQueryData ↦ Z.rankTupleAtStagePart q.fullTuple :=
    RecursiveIn.comp (α := HomogeneityQueryData) (β := List ℕ) (σ := ℕ × List ℕ)
      (f := Z.rankTupleAtStagePart) (g := HomogeneityQueryData.fullTuple)
      Z.rankTupleAtStagePart_recursiveIn (primrec_fullTuple.to_comp.computableIn (O := E))
  have hn₁ : ComputableIn E fun y : ReqIn₁ ↦ y.1.domainTuple.length :=
    ComputableIn.comp (α := ReqIn₁) (β := HomogeneityQueryData) (σ := ℕ)
      (f := fun q ↦ q.domainTuple.length) (g := fun y ↦ y.1)
      ((Primrec.list_length.comp HomogeneityQueryData.primrec_domainTuple).to_comp.computableIn
        (O := E)) ComputableIn.fst
  have hm₁ : ComputableIn E fun y : ReqIn₁ ↦ memberIdx K W i y.2.1 :=
    ComputableIn.comp (α := ReqIn₁) (β := ℕ) (σ := ℕ) (f := memberIdx K W i) (g := fun y ↦ y.2.1)
      (memberIdx_computableIn K W i hOE) (ComputableIn.fst.comp ComputableIn.snd)
  have hu₁ : ComputableIn E fun y : ReqIn₁ ↦ y.2.2 := ComputableIn.snd.comp ComputableIn.snd
  have htake₁ : ComputableIn E fun y : ReqIn₁ ↦ y.2.2.take y.1.domainTuple.length :=
    ComputableIn₂.comp (α := ReqIn₁) (β := List ℕ) (γ := ℕ) (σ := List ℕ)
      (f := fun l n ↦ l.take n) (g := fun y ↦ y.2.2) (h := fun y ↦ y.1.domainTuple.length)
      ((Primrec₂.swap Primrec.list_take).to_comp.computableIn₂ (O := E)) hu₁ hn₁
  have hchp₁ : RecursiveIn E fun y : ReqIn₁ ↦
      chpSel (memberIdx K W i y.2.1) (y.2.2.take y.1.domainTuple.length) :=
    RecursiveIn.comp (α := ReqIn₁) (β := ℕ × List ℕ) (σ := ℕ) (f := fun p ↦ chpSel p.1 p.2)
      (g := fun y ↦ (memberIdx K W i y.2.1, y.2.2.take y.1.domainTuple.length)) hchp
      (ComputableIn.pair (α := ReqIn₁) (β := ℕ) (γ := List ℕ) (f := fun y ↦ memberIdx K W i y.2.1)
        (g := fun y ↦ y.2.2.take y.1.domainTuple.length) hm₁ htake₁)
  have hdrop₂ : ComputableIn E fun z : ReqIn₂ ↦ z.1.2.2.drop z.1.1.domainTuple.length :=
    ComputableIn₂.comp (α := ReqIn₂) (β := List ℕ) (γ := ℕ) (σ := List ℕ)
      (f := fun l n ↦ l.drop n) (g := fun z ↦ z.1.2.2) (h := fun z ↦ z.1.1.domainTuple.length)
      ((Primrec₂.swap Primrec.list_drop).to_comp.computableIn₂ (O := E))
      (hu₁.comp ComputableIn.fst) (hn₁.comp ComputableIn.fst)
  have hchp₂ : RecursiveIn E fun z : ReqIn₂ ↦
      chpSel (memberIdx K W i z.1.2.1) (z.1.2.2.drop z.1.1.domainTuple.length) :=
    RecursiveIn.comp (α := ReqIn₂) (β := ℕ × List ℕ) (σ := ℕ) (f := fun p ↦ chpSel p.1 p.2)
      (g := fun z ↦ (memberIdx K W i z.1.2.1, z.1.2.2.drop z.1.1.domainTuple.length)) hchp
      (ComputableIn.pair (α := ReqIn₂) (β := ℕ) (γ := List ℕ)
        (f := fun z ↦ memberIdx K W i z.1.2.1)
        (g := fun z ↦ z.1.2.2.drop z.1.1.domainTuple.length) (hm₁.comp ComputableIn.fst) hdrop₂)
  have hgens : ComputableIn E fun w : ReqIn₂ × ℕ ↦ (K.gens w.2).take w.1.1.1.domainTuple.length :=
    ComputableIn₂.comp (α := ReqIn₂ × ℕ) (β := List ℕ) (γ := ℕ) (σ := List ℕ)
      (f := fun l n ↦ l.take n) (g := fun w ↦ K.gens w.2)
      (h := fun w ↦ w.1.1.1.domainTuple.length)
      ((Primrec₂.swap Primrec.list_take).to_comp.computableIn₂ (O := E))
      (ComputableIn.comp (α := ReqIn₂ × ℕ) (β := ℕ) (σ := List ℕ) (f := K.gens)
        (g := fun w ↦ w.2) (RecursiveIn.mono hOE K.gens_computableIn) ComputableIn.snd)
      (hn₁.comp (ComputableIn.fst.comp ComputableIn.fst))
  have hreq : ComputableIn E fun w : ReqIn₂ × ℕ ↦
      (⟨w.1.2, w.1.1.2.1, w.2, w.1.1.2.2.take w.1.1.1.domainTuple.length,
        (K.gens w.2).take w.1.1.1.domainTuple.length⟩ : RequirementData) :=
    ComputableIn.encode_iff.1
      ((ComputableIn.encode.comp
        (ComputableIn.pair (α := ReqIn₂ × ℕ) (β := ℕ) (γ := ℕ × ℕ × Tuple ℕ × Tuple ℕ)
          (f := fun w ↦ w.1.2)
          (g := fun w ↦ (w.1.1.2.1, w.2, w.1.1.2.2.take w.1.1.1.domainTuple.length,
            (K.gens w.2).take w.1.1.1.domainTuple.length))
          (ComputableIn.snd.comp ComputableIn.fst)
          (ComputableIn.pair (α := ReqIn₂ × ℕ) (β := ℕ) (γ := ℕ × Tuple ℕ × Tuple ℕ)
            (f := fun w ↦ w.1.1.2.1)
            (g := fun w ↦ (w.2, w.1.1.2.2.take w.1.1.1.domainTuple.length,
              (K.gens w.2).take w.1.1.1.domainTuple.length))
            (ComputableIn.fst.comp (ComputableIn.snd.comp (ComputableIn.fst.comp ComputableIn.fst)))
            (ComputableIn.pair (α := ReqIn₂ × ℕ) (β := ℕ) (γ := Tuple ℕ × Tuple ℕ)
              (f := fun w ↦ w.2)
              (g := fun w ↦ (w.1.1.2.2.take w.1.1.1.domainTuple.length,
                (K.gens w.2).take w.1.1.1.domainTuple.length))
              ComputableIn.snd
              (ComputableIn.pair (α := ReqIn₂ × ℕ) (β := Tuple ℕ) (γ := Tuple ℕ)
                (f := fun w ↦ w.1.1.2.2.take w.1.1.1.domainTuple.length)
                (g := fun w ↦ (K.gens w.2).take w.1.1.1.domainTuple.length)
                (htake₁.comp (ComputableIn.fst.comp ComputableIn.fst)) hgens))))).of_eq
        fun _ ↦ rfl)
  exact (RecursiveIn.bind hpull
    (RecursiveIn.bind hchp₁ (RecursiveIn.map hchp₂ hreq.to₂).to₂).to₂).of_eq fun _ ↦ rfl

theorem selectPart_recursiveIn (hchp : RecursiveIn E fun p : ℕ × List ℕ ↦ chpSel p.1 p.2) :
    RecursiveIn E (selectPart Z chpSel) := by
  have hc : ComputableIn E fun q : HomogeneityQueryData ↦
      decide (q.domainTuple.length = q.imageTuple.length) :=
    ((Primrec.eq (α := ℕ)).decide.comp
      (Primrec.list_length.comp HomogeneityQueryData.primrec_domainTuple)
      (Primrec.list_length.comp HomogeneityQueryData.primrec_imageTuple)).to_comp.computableIn
  have ho : ComputableIn E matchedQuery? :=
    ComputableIn.ite (c := fun q : HomogeneityQueryData ↦
      q.domainTuple.length = q.imageTuple.length) hc ComputableIn.option_some
      (ComputableIn.const Option.none)
  have hf : ComputableIn E fallbackAnswer :=
    ComputableIn.comp (α := HomogeneityQueryData) (β := Tuple ℕ × ℕ) (σ := HomogeneityAnswerData)
      (f := fun p ↦ ⟨p.1, p.2⟩) (g := fun q ↦ (q.domainTuple ++ [q.newPoint], q.newPoint))
      (primrec_homogeneityAnswerData.to_comp.computableIn (O := E))
      ((Primrec.pair (Primrec.list_append.comp HomogeneityQueryData.primrec_domainTuple
        (Primrec.list_cons.comp HomogeneityQueryData.primrec_newPoint (Primrec.const [])))
        HomogeneityQueryData.primrec_newPoint).to_comp.computableIn (O := E))
  have hg : RecursiveIn E fun p : HomogeneityQueryData × HomogeneityQueryData ↦
      (requirementPart Z chpSel p.2).bind (fromRequirementPart Z) :=
    RecursiveIn.comp (α := HomogeneityQueryData × HomogeneityQueryData)
      (β := HomogeneityQueryData) (σ := HomogeneityAnswerData)
      (f := fun q ↦ (requirementPart Z chpSel q).bind (fromRequirementPart Z)) (g := fun p ↦ p.2)
      (RecursiveIn.bind (requirementPart_recursiveIn Z chpSel hchp)
        ((fromRequirementPart_recursiveIn Z).comp ComputableIn.snd).to₂)
      ComputableIn.snd
  exact (RecursiveIn.option_casesOn_right ho hf hg.to₂).of_eq fun _ ↦ rfl

end EffectivityLimit

/-! ### The search and the payload, semantically -/

section Firing

variable {K : PartialAgeIn O L} {W : PartialCAPWitness E K} {i : ℕ}

/-- A value of the search is a firing stage. -/
theorem firesAt_of_mem_firingSearch {e s : ℕ} (h : s ∈ firingSearch K W i e) :
    (schedule K W i).FiresAt e s := by
  have ht : firesTest K W i e s = true := Nat.rfind_some_spec h
  exact firesAt_iff_pick.2 (of_decide_eq_true ht)

/-- The search halts on a code that fires. -/
theorem firingSearch_dom {e s : ℕ} (h : (schedule K W i).FiresAt e s) :
    (firingSearch K W i e).Dom :=
  Nat.rfind_some_dom_iff.2 ⟨s, decide_eq_true (firesAt_iff_pick.1 h)⟩

theorem mem_payloadPart_iff {s : ℕ} {q : RequirementData} {D : AmalgamationDiagramData} :
    D ∈ payloadPart K W i s q ↔
      ∃ δ ∈ K.transportPart (run K W i s).stages q.chainStage s,
        ∃ F ∈ K.compPart δ (q.chainMap (run K W i s).dHist),
          D ∈ W.sel (PotentialSpanData.ofPair (F, q.targetMap)) := by
  simp only [payloadPart, Part.mem_bind_iff]

/-- **The payload is the run's own diagram.** At the firing stage of `q`, the recomputed payload
halts, and every value of it is the diagram the run extended by. -/
theorem payloadPart_spec {q : RequirementData} {s : ℕ}
    (hfire : (schedule K W i).FiresAt (encode q) s) :
    (payloadPart K W i s q).Dom ∧ ∀ D ∈ payloadPart K W i s q,
      run K W i (s + 1) = (run K W i s).capExtension (encode q) D := by
  obtain ⟨q', hq', δ, hδ, F, hF, D, hD, hrun⟩ := exists_capExtension_of_firesAt hfire
  rw [RequirementData.decode_encode] at hq'
  obtain rfl := Option.some.inj hq'
  refine ⟨Part.dom_iff_mem.2 ⟨D, mem_payloadPart_iff.2 ⟨δ, hδ, F, hF, hD⟩⟩, fun D' hD' ↦ ?_⟩
  obtain ⟨δ', hδ', F', hF', hD'⟩ := mem_payloadPart_iff.1 hD'
  obtain rfl := Part.mem_unique hδ' hδ
  obtain rfl := Part.mem_unique hF' hF
  rw [Part.mem_unique hD' hD]
  exact hrun

/-- At the firing stage, the run's step is the payload's left leg. -/
theorem runStep_eq_of_mem_payloadPart {q : RequirementData} {s : ℕ}
    (hfire : (schedule K W i).FiresAt (encode q) s) {D : AmalgamationDiagramData}
    (hD : D ∈ payloadPart K W i s q) : runStep K W i s = D.leftToApex := by
  refine runStep_eq (rec := ⟨D.leftToApex.codIdx, D.leftToApex⟩) ?_
  rw [(payloadPart_spec hfire).2 D hD, RunState.stages_capExtension,
    ← run_stages_length (K := K) (W := W) (i := i) s]
  exact List.getElem?_concat_length

/-- **The payload's unconditional shape**: its diagram is well-shaped for the span, its left leg is
the run's step into the member at `s + 1`, and its right leg is well-formed, running from the
requirement's target member into that same member. No actualness of the requirement is used. -/
theorem payloadPart_unconditional {q : RequirementData} {s : ℕ}
    (hfire : (schedule K W i).FiresAt (encode q) s) {D : AmalgamationDiagramData}
    (hD : D ∈ payloadPart K W i s q) :
    q.chainStage ≤ s ∧ D.rightToApex.domIdx = q.targetIdx ∧
      D.rightToApex.codIdx = memberIdx K W i (s + 1) ∧ K.PartialWellFormed D.rightToApex := by
  obtain ⟨q', hq', hr', -⟩ := exists_decode_of_pick (firesAt_iff_pick.1 hfire)
  rw [RequirementData.decode_encode] at hq'
  obtain rfl := Option.some.inj hq'
  obtain ⟨δ, -, F, -, hsel⟩ := mem_payloadPart_iff.1 hD
  obtain ⟨hshape, -, hwf⟩ := W.unconditional _ D hsel
  refine ⟨hr', hshape.2.1, ?_, hwf⟩
  rw [← hshape.2.2, ← runStep_eq_of_mem_payloadPart hfire hD, runStep_codIdx]

end Firing

/-! ### The square at the payload -/

section Square

variable {K : PartialAgeIn O L} {W : PartialCAPWitness E K} {i : ℕ} {hOE : O ⊆ E}
  {h0 : (K.domainAt i).Nonempty} (Z : (runChain K W i hOE h0).LimitIn)

/-- **Conditional soundness at the recomputed payload.** When the requirement's two coded maps are
actual, the payload's right leg is actual, and its square — through the transported chain map and
the run's step — closes in the limit. The layer-1 square of `exists_one_point_extension`, at a
given firing stage and a given payload rather than existentially. -/
theorem exists_rightToApex_square {q : RequirementData} {s : ℕ}
    (hfire : (schedule K W i).FiresAt (encode q) s) {D : AmalgamationDiagramData}
    (hD : D ∈ payloadPart K W i s q)
    {f : (K.memberAt q.memberIdx).domain ↪[L] (K.memberAt (memberIdx K W i q.chainStage)).domain}
    (hf : K.PartialRealizes (q.chainMap (memberIdx K W i)) f)
    {g : (K.memberAt q.memberIdx).domain ↪[L] (K.memberAt q.targetIdx).domain}
    (hg : K.PartialRealizes q.targetMap g) :
    ∃ gr : (K.memberAt q.targetIdx).domain ↪[L] (K.memberAt (memberIdx K W i (s + 1))).domain,
      K.PartialRealizesAt D.rightToApex q.targetIdx (memberIdx K W i (s + 1)) gr ∧
        ∀ x, Z.stageEmbedding (s + 1) (runStageEquiv K W i hOE h0 (s + 1) (gr (g x))) =
          Z.stageEmbedding q.chainStage (runStageEquiv K W i hOE h0 q.chainStage (f x)) := by
  have hp := firesAt_iff_pick.1 hfire
  obtain ⟨q', hq', hr, -⟩ := exists_decode_of_pick hp
  rw [RequirementData.decode_encode] at hq'
  obtain rfl := Option.some.inj hq'
  have hf' : K.PartialIsEmbedding (q.chainMap (run K W i s).dHist) := by
    rw [chainMap_run_eq hr]; exact ⟨f, hf⟩
  obtain ⟨δ, hδ, F, hF, D', hD', -, -, hcomm, -⟩ :=
    exists_square_of_fire (W := W) (run_runInvariant s) hp (RequirementData.decode_encode q) hf'
      ⟨g, hg⟩
  obtain ⟨δ₀, hδ₀, F₀, hF₀, hsel⟩ := mem_payloadPart_iff.1 hD
  obtain rfl := Part.mem_unique hδ₀ hδ
  obtain rfl := Part.mem_unique hF₀ hF
  obtain rfl := Part.mem_unique hsel hD'
  have hstep := runStep_eq_of_mem_payloadPart hfire hD
  obtain ⟨δ', hδ', hδdom, hδcod, ⟨δr₀, hδr₀⟩⟩ :=
    (run_runInvariant (K := K) (W := W) (i := i) s).exists_transport hr
  obtain rfl := Part.mem_unique hδ' hδ₀
  obtain ⟨δr, hδr⟩ : ∃ δr : (K.memberAt (memberIdx K W i q.chainStage)).domain ↪[L]
      (K.memberAt (memberIdx K W i s)).domain,
      K.PartialRealizesAt δ' (memberIdx K W i q.chainStage) (memberIdx K W i s) δr :=
    ⟨_, hδr₀.realizesAt_of_eq (hδdom.trans (dHist_run_eq hr)) hδcod⟩
  -- the square, at named indices
  obtain ⟨d, m₁, m₂, apex, fl, fr, gl, gr, hfl, hfr, hgl, hgr, hsq⟩ := hcomm
  rw [PotentialSpanData.ofPair_left] at hfl
  rw [PotentialSpanData.ofPair_right] at hfr
  rw [chainMap_run_eq hr] at hF₀
  obtain ⟨v, hv, rfl⟩ := (K.mem_compPart_iff).1 hF₀
  obtain rfl : q.memberIdx = d := hfl.1
  obtain rfl : memberIdx K W i s = m₁ := hδcod.symm.trans hfl.2.1
  obtain rfl : q.targetIdx = m₂ := hfr.2.1
  obtain rfl : memberIdx K W i (s + 1) = apex := by rw [← hgl.2.1, ← hstep, runStep_codIdx]
  have hfr' : fr = g := hfr.unique ⟨rfl, rfl, hg⟩
  have hfl' : fl = δr.comp f := by
    obtain ⟨hlen, hcoord⟩ := hf
    refine hfl.unique ⟨rfl, hδcod, hlen.trans hv.length_eq, fun k ↦ ?_⟩
    have hk : k.1 < (q.chainMap (memberIdx K W i)).rangeTuple.length := lt_of_lt_of_eq k.2 hlen
    have h₁ := (List.forall₂_iff_get.1 hv).2 k.1 hk (by rw [← hv.length_eq]; exact hk)
    have h₂ : (q.chainMap (memberIdx K W i)).rangeTuple.get ⟨k.1, hk⟩ =
        ((f (K.gensView q.memberIdx k) : (K.memberAt (memberIdx K W i q.chainStage)).domain) :
          ℕ) :=
      (hcoord k).symm
    rw [h₂] at h₁
    exact Part.mem_unique (hδr.mem_applyPotentialPart (f (K.gensView q.memberIdx k)).2) h₁
  refine ⟨gr, hgr, fun x ↦ ?_⟩
  have hsq : gl (δr (f x)) = gr (g x) := by
    have := DFunLike.congr_fun hsq x
    rw [hfl', hfr'] at this
    exact this
  rw [← hsq, ← stageEmbedding_runStep hOE h0 Z hstep hgl (δr (f x)),
    ← stageEmbedding_transportPart hOE h0 Z hr hδ₀ hδr (f x)]

end Square

/-! ### Members in ω -/

section OmegaMember

variable {K : PartialAgeIn O L} {W : PartialCAPWitness E K} {i : ℕ} {hOE : O ⊆ E}
  {h0 : (K.domainAt i).Nonempty} (Z : (runChain K W i hOE h0).LimitIn)

/-- The member recorded at stage `t`, carried into ω by the recoded stage embedding. -/
noncomputable def omegaMember (t : ℕ) :
    @Language.Embedding L (K.memberAt (memberIdx K W i t)).domain ℕ _ Z.presentation.rankStr :=
  letI : L.Structure ℕ := Z.presentation.rankStr
  (Z.omegaStageEmbedding t).comp (runStageEquiv K W i hOE h0 t).toEmbedding

theorem omegaMember_apply (t : ℕ) (x : (K.memberAt (memberIdx K W i t)).domain) :
    omegaMember Z t x = Z.omegaStageEmbedding t (runStageEquiv K W i hOE h0 t x) :=
  rfl

/-- The program computes `omegaMember`. -/
theorem omegaMember_mem_rankStageMap (t : ℕ) (x : (K.memberAt (memberIdx K W i t)).domain) :
    omegaMember Z t x ∈ Z.rankStageMap t (x : ℕ) :=
  Z.omegaStageEmbedding_apply_mem t (runStageEquiv K W i hOE h0 t x)

theorem eq_omegaMember_of_mem_rankStageMap {t y : ℕ} {x : ℕ}
    (hx : x ∈ K.domainAt (memberIdx K W i t)) (hy : y ∈ Z.rankStageMap t x) :
    y = omegaMember Z t ⟨x, hx⟩ :=
  Part.mem_unique hy (omegaMember_mem_rankStageMap Z t ⟨x, hx⟩)

/-- **Every earlier stage element lands in the range of a later member**, in ω: transport it
forward, and the recoded stage embeddings agree along transport. -/
theorem omegaStageEmbedding_mem_range {t T : ℕ} (htT : t ≤ T) {z : ℕ}
    (hz : z ∈ ((runChain K W i hOE h0).stageAt t).domain) :
    Z.omegaStageEmbedding t ⟨z, hz⟩ ∈ Set.range (omegaMember Z T) := by
  obtain ⟨y, hy, -⟩ := CeStructureChainIn.exists_transport_mem htT hz
  obtain ⟨hy', heq⟩ := Z.omegaStageEmbedding_transport htT hz hy
  exact ⟨(runStageEquiv K W i hOE h0 T).symm ⟨y, hy'⟩, by
    rw [omegaMember_apply, Language.Equiv.apply_symm_apply, heq]⟩

/-- **`γ` names the apex member in ω**: the values of the generator traversal are `omegaMember`'s,
position by position. -/
theorem getElem?_of_mem_listMapPart {t : ℕ} {γ : List ℕ}
    (hγ : γ ∈ listMapPart (Z.rankStageMap t) (K.gens (memberIdx K W i t))) :
    γ.length = (K.gens (memberIdx K W i t)).length ∧
      ∀ k : Fin (K.gens (memberIdx K W i t)).length,
        γ[(k : ℕ)]? = Option.some (omegaMember Z t (K.gensView (memberIdx K W i t) k)) := by
  have h₂ := mem_listMapPart_iff.1 hγ
  refine ⟨h₂.length_eq.symm, fun k ↦ ?_⟩
  obtain ⟨b, hb, hbv⟩ := h₂.exists_getElem?_right
    (List.getElem?_eq_getElem (l := K.gens (memberIdx K W i t)) k.2)
  rw [hb, eq_omegaMember_of_mem_rankStageMap Z (K.gens_mem_domainAt k) hbv]
  rfl

end OmegaMember

/-! ### The selector's clauses -/

section Clauses

variable {K : PartialAgeIn O L} {W : PartialCAPWitness E K} {i : ℕ} {hOE : O ⊆ E}
  {h0 : (K.domainAt i).Nonempty} (Z : (runChain K W i hOE h0).LimitIn)
  (chpSel : ℕ → List ℕ →. ℕ)

theorem mem_requirementPart_iff {q : HomogeneityQueryData} {req : RequirementData} :
    req ∈ requirementPart Z chpSel q ↔
      ∃ p ∈ Z.rankTupleAtStagePart q.fullTuple,
        ∃ a ∈ chpSel (memberIdx K W i p.1) (p.2.take q.domainTuple.length),
          ∃ k ∈ chpSel (memberIdx K W i p.1) (p.2.drop q.domainTuple.length),
            req = queryRequirement K q.domainTuple.length p a k := by
  simp only [requirementPart, Part.mem_bind_iff, Part.mem_map_iff, eq_comm]

theorem mem_fromRequirementPart_iff {req : RequirementData} {ans : HomogeneityAnswerData} :
    ans ∈ fromRequirementPart Z req ↔
      ∃ s ∈ firingSearch K W i (encode req), ∃ D ∈ payloadPart K W i s req,
        ∃ γ ∈ listMapPart (Z.rankStageMap (s + 1)) (K.gens (memberIdx K W i (s + 1))),
          ∃ y ∈ Z.rankStageMap (s + 1) (D.rightToApex.rangeTuple.getLastD 0),
            ans = ⟨γ, y⟩ := by
  simp only [fromRequirementPart, answerPart, Part.mem_bind_iff, Part.mem_map_iff, eq_comm]

/-- The pulled-back tuple is a valid query at its stage's member. -/
theorem mem_domainAt_of_mem_pull {l : List ℕ} {p : ℕ × List ℕ}
    (hp : p ∈ Z.rankTupleAtStagePart l) : ∀ y ∈ p.2, y ∈ K.domainAt (memberIdx K W i p.1) := by
  intro y hy
  have h := Z.mem_domainAt_of_mem_rankTupleAtStagePart hp y hy
  rwa [runChain_stage_domain] at h

/-- The widths of a matched query's pulled tuple and of its two CHP representatives. -/
theorem query_widths (hchpSpec : K.MappedCHPSpec chpSel) {q : HomogeneityQueryData}
    (hlen : q.domainTuple.length = q.imageTuple.length) {p : ℕ × List ℕ}
    (hp : p ∈ Z.rankTupleAtStagePart q.fullTuple) {a k : ℕ}
    (ha : a ∈ chpSel (memberIdx K W i p.1) (p.2.take q.domainTuple.length))
    (hk : k ∈ chpSel (memberIdx K W i p.1) (p.2.drop q.domainTuple.length)) :
    p.2.length = 2 * q.domainTuple.length + 1 ∧
      K.PartialIsEmbedding (PotentialEmbeddingData.ofTriple
        (a, memberIdx K W i p.1, p.2.take q.domainTuple.length)) ∧
      K.PartialIsEmbedding (PotentialEmbeddingData.ofTriple
        (k, memberIdx K W i p.1, p.2.drop q.domainTuple.length)) ∧
      (K.gens a).length = q.domainTuple.length ∧ (K.gens k).length = q.domainTuple.length + 1 := by
  have hu : p.2.length = 2 * q.domainTuple.length + 1 := by
    rw [Z.rankTupleAtStagePart_length hp, HomogeneityQueryData.fullTuple, List.length_append,
      List.length_append, List.length_singleton, ← hlen]
    omega
  have hval := mem_domainAt_of_mem_pull Z hp
  obtain ⟨a', ha', hae⟩ := hchpSpec _ _ fun y hy ↦ hval y (List.mem_of_mem_take hy)
  obtain ⟨k', hk', hke⟩ := hchpSpec _ _ fun y hy ↦ hval y (List.mem_of_mem_drop hy)
  obtain rfl := Part.mem_unique ha' ha
  obtain rfl := Part.mem_unique hk' hk
  refine ⟨hu, hae, hke, ?_, ?_⟩
  · refine hae.length.trans ?_
    change (p.2.take q.domainTuple.length).length = _
    rw [List.length_take, hu]
    omega
  · refine hke.length.trans ?_
    change (p.2.drop q.domainTuple.length).length = _
    rw [List.length_drop, hu]
    omega

/-- **The payload's right leg ends in the apex member**, with the width of `A_k`: its last
coordinate exists and lies in the member at `s + 1`. Only well-formedness is used. -/
theorem getLastD_mem_domainAt (hchpSpec : K.MappedCHPSpec chpSel) {q : HomogeneityQueryData}
    (hlen : q.domainTuple.length = q.imageTuple.length) {p : ℕ × List ℕ}
    (hp : p ∈ Z.rankTupleAtStagePart q.fullTuple) {a k : ℕ}
    (ha : a ∈ chpSel (memberIdx K W i p.1) (p.2.take q.domainTuple.length))
    (hk : k ∈ chpSel (memberIdx K W i p.1) (p.2.drop q.domainTuple.length)) {s : ℕ}
    (hs : s ∈ firingSearch K W i (encode (queryRequirement K q.domainTuple.length p a k)))
    {D : AmalgamationDiagramData}
    (hD : D ∈ payloadPart K W i s (queryRequirement K q.domainTuple.length p a k)) :
    D.rightToApex.rangeTuple.length = q.domainTuple.length + 1 ∧
      D.rightToApex.rangeTuple[q.domainTuple.length]? =
        Option.some (D.rightToApex.rangeTuple.getLastD 0) ∧
      D.rightToApex.rangeTuple.getLastD 0 ∈ K.domainAt (memberIdx K W i (s + 1)) := by
  obtain ⟨-, -, -, -, hkw⟩ := query_widths Z chpSel hchpSpec hlen hp ha hk
  obtain ⟨-, hdom, hcod, hwf⟩ := payloadPart_unconditional (firesAt_of_mem_firingSearch hs) hD
  have hlenR : D.rightToApex.rangeTuple.length = q.domainTuple.length + 1 := by
    rw [← hwf.length, hdom]
    exact hkw
  have hget : D.rightToApex.rangeTuple[q.domainTuple.length]? =
      Option.some (D.rightToApex.rangeTuple.getLastD 0) := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, hlenR, Nat.add_sub_cancel,
      List.getElem?_eq_getElem (by omega)]
    rfl
  refine ⟨hlenR, hget, ?_⟩
  rw [← hcod]
  exact hwf.carrierValid _ (List.mem_of_getElem? hget)

variable (cert : Z.presentation.InfinitudeCertificate)

/-- **The apex member's ω-image is the answer's canonical member.** -/
theorem canonicalAge_domainAt_γ {t : ℕ} {γ : List ℕ}
    (hγ : γ ∈ listMapPart (Z.rankStageMap t) (K.gens (memberIdx K W i t))) :
    (Z.omegaStructure cert).canonicalAge.domainAt (encode γ) = Set.range (omegaMember Z t) := by
  obtain ⟨hlen, hpos⟩ := getElem?_of_mem_listMapPart Z hγ
  exact (Z.omegaStructure cert).canonicalAge_domainAt_eq_range (omegaMember Z t)
    (range_view_eq_of_getElem? hlen hpos)

/-- **Clause 1, unconditional**: `D_d⃗ ⊆ D_γ⃗`. Each entry of `d⃗` is the ω-image of a pulled
stage element at `r ≤ s + 1`, hence in the apex member's image. -/
theorem extends_domain_of_mem (hrep : Z.RepresentedByRawRep) {q : HomogeneityQueryData}
    {p : ℕ × List ℕ} (hp : p ∈ Z.rankTupleAtStagePart q.fullTuple) {a k s : ℕ}
    (hs : s ∈ firingSearch K W i (encode (queryRequirement K q.domainTuple.length p a k)))
    {D : AmalgamationDiagramData}
    (hD : D ∈ payloadPart K W i s (queryRequirement K q.domainTuple.length p a k)) {γ : List ℕ}
    (hγ : γ ∈ listMapPart (Z.rankStageMap (s + 1)) (K.gens (memberIdx K W i (s + 1)))) :
    (Z.omegaStructure cert).canonicalAge.domainAt (encode q.domainTuple) ⊆
      (Z.omegaStructure cert).canonicalAge.domainAt (encode γ) := by
  obtain ⟨hrs, -⟩ := payloadPart_unconditional (firesAt_of_mem_firingSearch hs) hD
  have hco := Z.forall₂_omegaStageEmbedding hrep hp
  refine (Z.omegaStructure cert).canonicalAge_domainAt_subset fun z hz ↦ ?_
  rw [allTupleFor_encode] at hz
  rw [canonicalAge_domainAt_γ Z cert hγ]
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hz
  have hfull : q.fullTuple[j]? = Option.some q.domainTuple[j] := by
    rw [HomogeneityQueryData.fullTuple, List.append_assoc, List.getElem?_append_left hj,
      List.getElem?_eq_getElem hj]
  obtain ⟨y, -, hy, hyv⟩ := hco.exists_getElem?_right hfull
  rw [← hyv]
  exact omegaStageEmbedding_mem_range Z (hrs.trans (Nat.le_succ s)) hy

/-- **Clause 2, unconditional**: `y ∈ D_γ⃗`. The right leg's last coordinate lies in the apex
member, by its well-formedness alone. -/
theorem imageOfNewPoint_mem_of_mem (hchpSpec : K.MappedCHPSpec chpSel)
    {q : HomogeneityQueryData} (hlen : q.domainTuple.length = q.imageTuple.length)
    {p : ℕ × List ℕ} (hp : p ∈ Z.rankTupleAtStagePart q.fullTuple) {a k : ℕ}
    (ha : a ∈ chpSel (memberIdx K W i p.1) (p.2.take q.domainTuple.length))
    (hk : k ∈ chpSel (memberIdx K W i p.1) (p.2.drop q.domainTuple.length)) {s : ℕ}
    (hs : s ∈ firingSearch K W i (encode (queryRequirement K q.domainTuple.length p a k)))
    {D : AmalgamationDiagramData}
    (hD : D ∈ payloadPart K W i s (queryRequirement K q.domainTuple.length p a k)) {γ : List ℕ}
    (hγ : γ ∈ listMapPart (Z.rankStageMap (s + 1)) (K.gens (memberIdx K W i (s + 1)))) {y : ℕ}
    (hy : y ∈ Z.rankStageMap (s + 1) (D.rightToApex.rangeTuple.getLastD 0)) :
    y ∈ (Z.omegaStructure cert).canonicalAge.domainAt (encode γ) := by
  obtain ⟨-, -, hw⟩ := getLastD_mem_domainAt Z chpSel hchpSpec hlen hp ha hk hs hD
  rw [canonicalAge_domainAt_γ Z cert hγ, eq_omegaMember_of_mem_rankStageMap Z hw hy]
  exact ⟨_, rfl⟩

/-- An indexed realizer, read positionally. -/
theorem PartialRealizesAt.getElem?_eq {K' : PartialAgeIn E L} {F : PotentialEmbeddingData}
    {d a : ℕ} {f : (K'.memberAt d).domain ↪[L] (K'.memberAt a).domain}
    (hf : K'.PartialRealizesAt F d a f) {j : ℕ} {x : (K'.memberAt d).domain}
    (hx : (K'.gens d)[j]? = Option.some (x : ℕ)) :
    F.rangeTuple[j]? = Option.some ((f x : (K'.memberAt a).domain) : ℕ) := by
  obtain ⟨rfl, rfl, h⟩ := hf
  exact getElem?_of_realizes (partialRealizesBetween_self.2 h) hx

/-- A member embedding into ω whose values on the recorded generators are read off a tuple has
that tuple's canonical member as its range. -/
theorem canonicalAge_domainAt_eq_range_of_getElem? {A : PartialAgeIn O L} {c : ℕ}
    (e : @Language.Embedding L (A.memberAt c).domain ℕ _ (Z.omegaStructure cert).inst)
    {t : Tuple ℕ} (hlen : t.length = (A.gens c).length)
    (hpos : ∀ (j : ℕ) (z : (A.memberAt c).domain), (A.gens c)[j]? = Option.some (z : ℕ) →
      t[j]? = Option.some (e z)) :
    (Z.omegaStructure cert).canonicalAge.domainAt (encode t) = Set.range e :=
  (Z.omegaStructure cert).canonicalAge_domainAt_eq_range e
    (range_view_eq_of_getElem? hlen fun k ↦ hpos k (A.gensView c k)
      (List.getElem?_eq_getElem (l := A.gens c) k.2))

/-- **Clause 3, conditional**: when `g` is actual, the one-point extension running back along it is
actual. The requirement's maps are then actual — `f` by CHP, `g` by factoring through `A_k`'s
image — so the payload's square closes, and the extension is the right leg read in ω. -/
theorem extension_actual_of_mem (hchpSpec : K.MappedCHPSpec chpSel) (hrep : Z.RepresentedByRawRep)
    {q : HomogeneityQueryData} (hlen : q.domainTuple.length = q.imageTuple.length)
    {p : ℕ × List ℕ} (hp : p ∈ Z.rankTupleAtStagePart q.fullTuple) {a k : ℕ}
    (ha : a ∈ chpSel (memberIdx K W i p.1) (p.2.take q.domainTuple.length))
    (hk : k ∈ chpSel (memberIdx K W i p.1) (p.2.drop q.domainTuple.length)) {s : ℕ}
    (hs : s ∈ firingSearch K W i (encode (queryRequirement K q.domainTuple.length p a k)))
    {D : AmalgamationDiagramData}
    (hD : D ∈ payloadPart K W i s (queryRequirement K q.domainTuple.length p a k)) {γ : List ℕ}
    (hγ : γ ∈ listMapPart (Z.rankStageMap (s + 1)) (K.gens (memberIdx K W i (s + 1)))) {y : ℕ}
    (hy : y ∈ Z.rankStageMap (s + 1) (D.rightToApex.rangeTuple.getLastD 0))
    (horig : (Z.omegaStructure cert).canonicalAge.PartialIsEmbedding q.originalMap) :
    (Z.omegaStructure cert).canonicalAge.PartialIsEmbedding (q.extensionMap ⟨γ, y⟩) := by
  letI : L.Structure ℕ := Z.presentation.rankStr
  obtain ⟨hu, hφe, hψe, hwa, hwk⟩ := query_widths Z chpSel hchpSpec hlen hp ha hk
  obtain ⟨φ, hφ⟩ : ∃ φ : (K.memberAt a).domain ↪[L] (K.memberAt (memberIdx K W i p.1)).domain,
      K.PartialRealizes (PotentialEmbeddingData.ofTriple
        (a, memberIdx K W i p.1, p.2.take q.domainTuple.length)) φ := hφe
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (K.memberAt k).domain ↪[L] (K.memberAt (memberIdx K W i p.1)).domain,
      K.PartialRealizes (PotentialEmbeddingData.ofTriple
        (k, memberIdx K W i p.1, p.2.drop q.domainTuple.length)) ψ := hψe
  have hco := Z.forall₂_omegaStageEmbedding hrep hp
  -- the pulled tuple's ω-image, position by position
  have hcoord : ∀ (j : ℕ) (w : (K.memberAt (memberIdx K W i p.1)).domain),
      p.2[j]? = Option.some (w : ℕ) → q.fullTuple[j]? = Option.some (omegaMember Z p.1 w) := by
    intro j w hw
    obtain ⟨b, hb, _, hbv⟩ := hco.exists_getElem?_left hw
    rw [hb, ← hbv]
    rfl
  -- `d⃗` is the ω-image of `A_a`'s generators through `φ`
  have hd_pos : ∀ (j : ℕ) (z : (K.memberAt a).domain), (K.gens a)[j]? = Option.some (z : ℕ) →
      q.domainTuple[j]? = Option.some (omegaMember Z p.1 (φ z)) := by
    intro j z hz
    have hj : j < q.domainTuple.length := by
      rw [← hwa]; exact (List.getElem?_eq_some_iff.1 hz).1
    have h₁ := getElem?_of_realizes (partialRealizesBetween_self.2 hφ) hz
    change (p.2.take q.domainTuple.length)[j]? = _ at h₁
    rw [List.getElem?_take_of_lt hj] at h₁
    have h₂ := hcoord j (φ z) h₁
    rwa [HomogeneityQueryData.fullTuple, List.append_assoc, List.getElem?_append_left hj] at h₂
  -- `c⃗ ++ [x]` is the ω-image of `A_k`'s generators through `ψ`
  have hc_pos : ∀ (j : ℕ) (z : (K.memberAt k).domain), (K.gens k)[j]? = Option.some (z : ℕ) →
      (q.imageTuple ++ [q.newPoint])[j]? = Option.some (omegaMember Z p.1 (ψ z)) := by
    intro j z hz
    have h₁ := getElem?_of_realizes (partialRealizesBetween_self.2 hψ) hz
    change (p.2.drop q.domainTuple.length)[j]? = _ at h₁
    rw [List.getElem?_drop] at h₁
    have h₂ := hcoord _ (ψ z) h₁
    rwa [HomogeneityQueryData.fullTuple, List.append_assoc,
      List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left] at h₂
  -- the three canonical members involved, as ranges
  have hrange_d : (Z.omegaStructure cert).canonicalAge.domainAt (encode q.domainTuple) =
      Set.range ((omegaMember Z p.1).comp φ) :=
    canonicalAge_domainAt_eq_range_of_getElem? Z cert _ hwa.symm hd_pos
  have hrange_c : (Z.omegaStructure cert).canonicalAge.domainAt
      (encode (q.imageTuple ++ [q.newPoint])) = Set.range ((omegaMember Z p.1).comp ψ) :=
    canonicalAge_domainAt_eq_range_of_getElem? Z cert _
      (by rw [List.length_append, List.length_singleton, hwk, hlen]) hc_pos
  have hrange_γ := canonicalAge_domainAt_γ Z cert hγ
  -- the original map, read positionally
  obtain ⟨g', hg'⟩ : ∃ g' : ((Z.omegaStructure cert).canonicalAge.memberAt
      (encode q.domainTuple)).domain ↪[L]
        ((Z.omegaStructure cert).canonicalAge.memberAt (encode q.imageTuple)).domain,
      (Z.omegaStructure cert).canonicalAge.PartialRealizes q.originalMap g' := horig
  have hg'_pos : ∀ (j : ℕ)
      (z : ((Z.omegaStructure cert).canonicalAge.memberAt (encode q.domainTuple)).domain),
      q.domainTuple[j]? = Option.some (z : ℕ) →
        q.imageTuple[j]? = Option.some ((g' z : ((Z.omegaStructure cert).canonicalAge.memberAt
          (encode q.imageTuple)).domain) : ℕ) := by
    intro j z hz
    refine getElem?_of_realizes (partialRealizesBetween_self.2 hg') ?_
    change (allTupleFor (encode q.domainTuple))[j]? = _
    rw [allTupleFor_encode]
    exact hz
  -- `g` pulled back to the members: `θ : A_a ↪ A_k`, by factoring through `A_k`'s image
  let crd := ((Z.omegaStructure cert).canonicalAge.memberAt (encode q.domainTuple)).codRestrict
    ((omegaMember Z p.1).comp φ) fun z ↦ by
      change _ ∈ (Z.omegaStructure cert).canonicalAge.domainAt (encode q.domainTuple)
      rw [hrange_d]; exact ⟨z, rfl⟩
  let ι : @Language.Embedding L (K.memberAt a).domain ℕ _ Z.presentation.rankStr :=
    ((Z.omegaStructure cert).canonicalAge.memberAt (encode q.imageTuple)).domainInclusion.comp
      (g'.comp crd)
  have hι : ∀ z, ι z ∈ ((omegaMember Z p.1).comp ψ).toHom.range := by
    intro z
    have hmem : ι z ∈ (Z.omegaStructure cert).canonicalAge.domainAt
        (encode (q.imageTuple ++ [q.newPoint])) := by
      refine (Z.omegaStructure cert).canonicalAge_domainAt_subset (fun w hw ↦ ?_) (g' (crd z)).2
      rw [allTupleFor_encode] at hw
      exact (Z.omegaStructure cert).mem_canonicalAge_domainAt_of_mem_gens
        (by rw [allTupleFor_encode]; exact List.mem_append_left _ hw)
    rw [hrange_c] at hmem
    obtain ⟨w, hw⟩ := hmem
    exact ⟨w, hw⟩
  obtain ⟨θ, hθ⟩ := exists_embedding_factor ι ((omegaMember Z p.1).comp ψ) hι
  -- `θ` carries `A_a`'s generators to the first `n` of `A_k`'s
  have hθ_pos : ∀ (j : ℕ) (z : (K.memberAt a).domain), (K.gens a)[j]? = Option.some (z : ℕ) →
      (K.gens k)[j]? = Option.some ((θ z : (K.memberAt k).domain) : ℕ) := by
    intro j z hz
    have hj : j < q.domainTuple.length := by
      rw [← hwa]; exact (List.getElem?_eq_some_iff.1 hz).1
    have hjk : j < (K.gens k).length := by omega
    have hw : (K.gens k)[j]? =
        Option.some (((⟨(K.gens k)[j], K.mem_domainAt_of_mem_gens (List.getElem_mem hjk)⟩ :
          (K.memberAt k).domain)) : ℕ) :=
      List.getElem?_eq_getElem hjk
    have hc := hc_pos j _ hw
    rw [List.getElem?_append_left (by rw [← hlen]; exact hj)] at hc
    have hgz := hg'_pos j (crd z) (hd_pos j z hz)
    have heq : ((omegaMember Z p.1).comp ψ)
        ⟨(K.gens k)[j], K.mem_domainAt_of_mem_gens (List.getElem_mem hjk)⟩ =
          ((omegaMember Z p.1).comp ψ) (θ z) := by
      rw [hθ z]
      exact Option.some.inj (hc.symm.trans hgz)
    rw [hw, ← ((omegaMember Z p.1).comp ψ).injective heq]
  have hθreal : K.PartialRealizes (PotentialEmbeddingData.ofTriple
      (a, k, (K.gens k).take q.domainTuple.length)) θ := by
    refine partialRealizesBetween_self.1 (realizes_of_getElem? ?_ fun j z hz ↦ ?_)
    · rw [List.length_take, hwk, hwa]; omega
    · have hj : j < q.domainTuple.length := by
        rw [← hwa]; exact (List.getElem?_eq_some_iff.1 hz).1
      rw [List.getElem?_take_of_lt hj]
      exact hθ_pos j z hz
  -- the payload's square, read in ω
  obtain ⟨gr, hgr, hsq⟩ :=
    exists_rightToApex_square Z (q := queryRequirement K q.domainTuple.length p a k)
      (firesAt_of_mem_firingSearch hs) hD (f := φ) hφ (g := θ) hθreal
  have hsqω : ∀ z, omegaMember Z (s + 1) (gr (θ z)) = omegaMember Z p.1 (φ z) := fun z ↦ by
    rw [omegaMember_apply, omegaMember_apply, CeStructureChainIn.LimitIn.omegaStageEmbedding_apply,
      CeStructureChainIn.LimitIn.omegaStageEmbedding_apply]
    exact congrArg _ (hsq z)
  -- the extension: back along `A_k`'s image, the right leg, and into the apex member's image
  let crc := ((Z.omegaStructure cert).canonicalAge.memberAt
    (encode (q.imageTuple ++ [q.newPoint]))).codRestrict ((omegaMember Z p.1).comp ψ) fun z ↦ by
      change _ ∈ (Z.omegaStructure cert).canonicalAge.domainAt _
      rw [hrange_c]; exact ⟨z, rfl⟩
  have hsurj : Function.Surjective crc := fun w ↦ by
    have hw : (w : ℕ) ∈ (Z.omegaStructure cert).canonicalAge.domainAt
        (encode (q.imageTuple ++ [q.newPoint])) := w.2
    rw [hrange_c] at hw
    obtain ⟨z, hz⟩ := hw
    exact ⟨z, Subtype.ext hz⟩
  let crγ := ((Z.omegaStructure cert).canonicalAge.memberAt (encode γ)).codRestrict
    (omegaMember Z (s + 1)) fun z ↦ by
      change _ ∈ (Z.omegaStructure cert).canonicalAge.domainAt _
      rw [hrange_γ]; exact ⟨z, rfl⟩
  refine ⟨crγ.comp (gr.comp (crc.equivOfSurjective hsurj).symm.toEmbedding), ?_⟩
  change (Z.omegaStructure cert).canonicalAge.PartialRealizes (PotentialEmbeddingData.ofTriple
    (encode (q.imageTuple ++ [q.newPoint]), encode γ, q.domainTuple ++ [y])) _
  refine partialRealizesBetween_self.1 (realizes_of_getElem? ?_ fun j w hw ↦ ?_)
  · change (allTupleFor (encode (q.imageTuple ++ [q.newPoint]))).length = _
    rw [allTupleFor_encode, List.length_append, List.length_append, hlen]
    rfl
  change (allTupleFor (encode (q.imageTuple ++ [q.newPoint])))[j]? = _ at hw
  rw [allTupleFor_encode] at hw
  -- the source point is the `j`-th generator of `A_k`
  have hj : j < q.domainTuple.length + 1 := by
    have := (List.getElem?_eq_some_iff.1 hw).1
    rw [List.length_append, List.length_singleton, ← hlen] at this
    exact this
  have hjk : j < (K.gens k).length := by omega
  set z := (crc.equivOfSurjective hsurj).symm w with hzdef
  have hzw : ((omegaMember Z p.1).comp ψ) z = (w : ℕ) := by
    have := congrArg Subtype.val ((crc.equivOfSurjective hsurj).apply_symm_apply w)
    exact this
  have hgk : (K.gens k)[j]? = Option.some (z : ℕ) := by
    have hw' : (K.gens k)[j]? =
        Option.some (((⟨(K.gens k)[j], K.mem_domainAt_of_mem_gens (List.getElem_mem hjk)⟩ :
          (K.memberAt k).domain)) : ℕ) :=
      List.getElem?_eq_getElem hjk
    have hc := hc_pos j _ hw'
    rw [hw] at hc
    have heq : ((omegaMember Z p.1).comp ψ)
        ⟨(K.gens k)[j], K.mem_domainAt_of_mem_gens (List.getElem_mem hjk)⟩ =
          ((omegaMember Z p.1).comp ψ) z := by
      rw [hzw]; exact (Option.some.inj hc).symm
    rw [hw', ((omegaMember Z p.1).comp ψ).injective heq]
  have hright := PartialRealizesAt.getElem?_eq hgr hgk
  change (q.domainTuple ++ [y])[j]? = Option.some (omegaMember Z (s + 1) (gr z))
  rcases Nat.lt_or_ge j q.domainTuple.length with hjn | hjn
  · -- an old generator: the square
    have hja : j < (K.gens a).length := by omega
    have hga : (K.gens a)[j]? =
        Option.some (((⟨(K.gens a)[j], K.mem_domainAt_of_mem_gens (List.getElem_mem hja)⟩ :
          (K.memberAt a).domain)) : ℕ) :=
      List.getElem?_eq_getElem hja
    have hθz : θ ⟨(K.gens a)[j], K.mem_domainAt_of_mem_gens (List.getElem_mem hja)⟩ = z :=
      Subtype.ext (Option.some.inj ((hθ_pos j _ hga).symm.trans hgk))
    rw [List.getElem?_append_left hjn, hd_pos j _ hga, ← hθz, hsqω]
  · -- the new point: the right leg's last coordinate
    obtain rfl : j = q.domainTuple.length := by omega
    obtain ⟨-, hlast, hmem⟩ := getLastD_mem_domainAt Z chpSel hchpSpec hlen hp ha hk hs hD
    rw [hlast] at hright
    rw [List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_cons_zero,
      eq_omegaMember_of_mem_rankStageMap Z hmem hy]
    exact congrArg _ (congrArg _ (Subtype.ext (Option.some.inj hright)))

end Clauses

/-! ### Totality and the package -/

section Package

variable {K : PartialAgeIn O L} {W : PartialCAPWitness E K} {i : ℕ} {hOE : O ⊆ E}
  {h0 : (K.domainAt i).Nonempty} (Z : (runChain K W i hOE h0).LimitIn)
  (chpSel : ℕ → List ℕ →. ℕ)

theorem selectPart_of_matched {q : HomogeneityQueryData}
    (hlen : q.domainTuple.length = q.imageTuple.length) :
    selectPart Z chpSel q = (requirementPart Z chpSel q).bind (fromRequirementPart Z) := by
  simp only [selectPart, matchedQuery?, if_pos hlen]

theorem selectPart_of_not_matched {q : HomogeneityQueryData}
    (hlen : ¬ q.domainTuple.length = q.imageTuple.length) :
    selectPart Z chpSel q = Part.some (fallbackAnswer q) := by
  simp only [selectPart, matchedQuery?, if_neg hlen]

/-- **The requirement of a matched query is admissible** — whether or not `g` is actual. This is
what makes the firing search halt on every matched query. -/
theorem queryRequirement_admissible (hchpSpec : K.MappedCHPSpec chpSel)
    {q : HomogeneityQueryData} (hlen : q.domainTuple.length = q.imageTuple.length)
    {p : ℕ × List ℕ} (hp : p ∈ Z.rankTupleAtStagePart q.fullTuple) {a k : ℕ}
    (ha : a ∈ chpSel (memberIdx K W i p.1) (p.2.take q.domainTuple.length))
    (hk : k ∈ chpSel (memberIdx K W i p.1) (p.2.drop q.domainTuple.length)) :
    K.Admissible (memberIdx K W i) (queryRequirement K q.domainTuple.length p a k) := by
  obtain ⟨hu, -, -, hwa, hwk⟩ := query_widths Z chpSel hchpSpec hlen hp ha hk
  refine ⟨⟨?_, ?_, ?_⟩, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · change (p.2.take q.domainTuple.length).length = (K.gens a).length
    rw [List.length_take, hu, hwa]; omega
  · change ((K.gens k).take q.domainTuple.length).length = (K.gens a).length
    rw [List.length_take, hwk, hwa]; omega
  · change (K.gens k).length = (K.gens a).length + 1
    rw [hwk, hwa]
  · exact mem_domainAt_of_mem_pull Z hp x (List.mem_of_mem_take hx)
  · exact K.mem_domainAt_of_mem_gens (List.mem_of_mem_take hx)

variable (hchpSpec : K.MappedCHPSpec chpSel) (cert : Z.presentation.InfinitudeCertificate)

include hchpSpec cert in
/-- **The program halts on every query**: the pullback under the certificate, the CHP calls on
valid queries, the firing search by fairness at an admissible requirement, the payload at its
firing stage, and the answer on the apex member. -/
theorem selectPart_dom (q : HomogeneityQueryData) : (selectPart Z chpSel q).Dom := by
  by_cases hlen : q.domainTuple.length = q.imageTuple.length
  swap
  · rw [selectPart_of_not_matched Z chpSel hlen]; trivial
  rw [selectPart_of_matched Z chpSel hlen]
  obtain ⟨p, hp⟩ := Part.dom_iff_mem.1 (Z.rankTupleAtStagePart_dom cert q.fullTuple)
  have hval := mem_domainAt_of_mem_pull Z hp
  obtain ⟨a, ha, -⟩ := hchpSpec _ _ fun y hy ↦ hval y (List.mem_of_mem_take hy)
  obtain ⟨k, hk, -⟩ := hchpSpec _ _ fun y hy ↦ hval y (List.mem_of_mem_drop hy)
  obtain ⟨s₀, hfire₀⟩ := exists_firesAt_of_admissible (K := K) (W := W) (i := i)
    (queryRequirement_admissible Z chpSel hchpSpec hlen hp ha hk)
  obtain ⟨s, hs⟩ := Part.dom_iff_mem.1 (firingSearch_dom hfire₀)
  have hfire := firesAt_of_mem_firingSearch hs
  obtain ⟨D, hD⟩ := Part.dom_iff_mem.1 (payloadPart_spec hfire).1
  obtain ⟨-, -, hw⟩ := getLastD_mem_domainAt Z chpSel hchpSpec hlen hp ha hk hs hD
  obtain ⟨γ, hγ⟩ := Part.dom_iff_mem.1 (listMapPart_dom_iff.2 fun x hx ↦
    Part.dom_iff_mem.2
      ⟨_, omegaMember_mem_rankStageMap Z (s + 1) ⟨x, K.mem_domainAt_of_mem_gens hx⟩⟩)
  refine Part.dom_iff_mem.2 ⟨⟨γ, omegaMember Z (s + 1) ⟨_, hw⟩⟩, ?_⟩
  refine Part.mem_bind_iff.2 ⟨_, (mem_requirementPart_iff Z chpSel).2
    ⟨p, hp, a, ha, k, hk, rfl⟩, (mem_fromRequirementPart_iff Z).2 ⟨s, hs, D, hD, γ, hγ, _,
      omegaMember_mem_rankStageMap Z (s + 1) ⟨_, hw⟩, rfl⟩⟩

/-- **The homogeneity selector**: the program, totalized once. -/
noncomputable def homogeneitySelect (q : HomogeneityQueryData) : HomogeneityAnswerData :=
  (selectPart Z chpSel q).get (selectPart_dom Z chpSel hchpSpec cert q)

theorem homogeneitySelect_mem (q : HomogeneityQueryData) :
    homogeneitySelect Z chpSel hchpSpec cert q ∈ selectPart Z chpSel q :=
  Part.get_mem _

/-- The answer to a matched query, unpacked into the pipeline's stages. -/
theorem exists_trace_of_matched {q : HomogeneityQueryData}
    (hlen : q.domainTuple.length = q.imageTuple.length) :
    ∃ p ∈ Z.rankTupleAtStagePart q.fullTuple,
      ∃ a ∈ chpSel (memberIdx K W i p.1) (p.2.take q.domainTuple.length),
        ∃ k ∈ chpSel (memberIdx K W i p.1) (p.2.drop q.domainTuple.length),
          ∃ s ∈ firingSearch K W i (encode (queryRequirement K q.domainTuple.length p a k)),
            ∃ D ∈ payloadPart K W i s (queryRequirement K q.domainTuple.length p a k),
              ∃ γ ∈ listMapPart (Z.rankStageMap (s + 1)) (K.gens (memberIdx K W i (s + 1))),
                ∃ y ∈ Z.rankStageMap (s + 1) (D.rightToApex.rangeTuple.getLastD 0),
                  homogeneitySelect Z chpSel hchpSpec cert q = ⟨γ, y⟩ := by
  have h := homogeneitySelect_mem Z chpSel hchpSpec cert q
  rw [selectPart_of_matched Z chpSel hlen, Part.mem_bind_iff] at h
  obtain ⟨req, hreq, hans⟩ := h
  obtain ⟨p, hp, a, ha, k, hk, rfl⟩ := (mem_requirementPart_iff Z chpSel).1 hreq
  obtain ⟨s, hs, D, hD, γ, hγ, y, hy, hans⟩ := (mem_fromRequirementPart_iff Z).1 hans
  exact ⟨p, hp, a, ha, k, hk, s, hs, D, hD, γ, hγ, y, hy, hans⟩

theorem homogeneitySelect_of_not_matched {q : HomogeneityQueryData}
    (hlen : ¬ q.domainTuple.length = q.imageTuple.length) :
    homogeneitySelect Z chpSel hchpSpec cert q = fallbackAnswer q := by
  have h := homogeneitySelect_mem Z chpSel hchpSpec cert q
  rw [selectPart_of_not_matched Z chpSel hlen] at h
  exact Part.mem_some_iff.1 h

/-- **The ω structure of the run's limit is computably homogeneous** (CHMM Definition 3.1), with
the selector above. -/
noncomputable def computablyHomogeneous (hrep : Z.RepresentedByRawRep)
    (hchp : RecursiveIn E fun p : ℕ × List ℕ ↦ chpSel p.1 p.2) :
    ComputablyHomogeneousIn E (Z.omegaStructure cert) where
  select := homogeneitySelect Z chpSel hchpSpec cert
  select_computableIn := RecursiveIn.computableIn_get (selectPart_recursiveIn Z chpSel hchp)
    (selectPart_dom Z chpSel hchpSpec cert)
  extends_domain q := by
    by_cases hlen : q.domainTuple.length = q.imageTuple.length
    · obtain ⟨p, hp, a, ha, k, hk, s, hs, D, hD, γ, hγ, y, hy, h⟩ :=
        exists_trace_of_matched Z chpSel hchpSpec cert hlen
      rw [h]
      exact extends_domain_of_mem Z cert hrep hp hs hD hγ
    · rw [homogeneitySelect_of_not_matched Z chpSel hchpSpec cert hlen]
      refine (Z.omegaStructure cert).canonicalAge_domainAt_subset fun x hx ↦ ?_
      rw [allTupleFor_encode] at hx
      exact (Z.omegaStructure cert).mem_canonicalAge_domainAt_of_mem_gens
        (by rw [allTupleFor_encode]; exact List.mem_append_left _ hx)
  imageOfNewPoint_mem q := by
    by_cases hlen : q.domainTuple.length = q.imageTuple.length
    · obtain ⟨p, hp, a, ha, k, hk, s, hs, D, hD, γ, hγ, y, hy, h⟩ :=
        exists_trace_of_matched Z chpSel hchpSpec cert hlen
      rw [h]
      exact imageOfNewPoint_mem_of_mem Z chpSel cert hchpSpec hlen hp ha hk hs hD hγ hy
    · rw [homogeneitySelect_of_not_matched Z chpSel hchpSpec cert hlen]
      exact (Z.omegaStructure cert).mem_canonicalAge_domainAt_of_mem_gens
        (by rw [allTupleFor_encode]; exact List.mem_append_right _ (List.mem_singleton_self _))
  extension_actual q horig := by
    by_cases hlen : q.domainTuple.length = q.imageTuple.length
    · obtain ⟨p, hp, a, ha, k, hk, s, hs, D, hD, γ, hγ, y, hy, h⟩ :=
        exists_trace_of_matched Z chpSel hchpSpec cert hlen
      rw [h]
      exact extension_actual_of_mem Z chpSel cert hchpSpec hrep hlen hp ha hk hs hD hγ hy horig
    · refine absurd ?_ hlen
      have := horig.length
      change (allTupleFor (encode q.domainTuple)).length = q.imageTuple.length at this
      rwa [allTupleFor_encode] at this

end Package

section Corollaries

variable {K : PartialAgeIn O L} {W : PartialCAPWitness E K} {i : ℕ} {hOE : O ⊆ E}
  {h0 : (K.domainAt i).Nonempty}

/-- **Computable homogeneity from the paper's hereditary selector**, for any limit of the run that
names its codes by raw representatives. -/
theorem nonempty_computablyHomogeneousIn (Z : (runChain K W i hOE h0).LimitIn)
    (hCHP : MappedPartialCHPIn E K) (hrep : Z.RepresentedByRawRep)
    (cert : Z.presentation.InfinitudeCertificate) :
    Nonempty (ComputablyHomogeneousIn E (Z.omegaStructure cert)) := by
  obtain ⟨sel, hsel, hspec⟩ := hCHP.exists_chpSpec
  exact ⟨computablyHomogeneous Z sel hspec cert hrep hsel⟩

/-- **At the run's canonical limit**, where representation by raw representatives is a theorem. -/
theorem toLimit_computablyHomogeneousIn (hCHP : MappedPartialCHPIn E K)
    (cert : ((runChain K W i hOE h0).toLimit
      (runChain_uniformEvaluators K W i hOE h0)).presentation.InfinitudeCertificate) :
    Nonempty (ComputablyHomogeneousIn E
      (((runChain K W i hOE h0).toLimit (runChain_uniformEvaluators K W i hOE h0)).omegaStructure
        cert)) :=
  nonempty_computablyHomogeneousIn _ hCHP (CeStructureChainIn.toLimit_representedByRawRep _ _)
    cert

end Corollaries

end PartialAgeIn

end FirstOrder.Language
