/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.AgeChainWitness
import ComputableModelTheory.ModelTheory.Computable.CeStructureChain
import ComputableModelTheory.ModelTheory.Computable.ChainHistory

/-!
# Assembling a c.e. structure chain from actual connecting maps

The generic recipe the CJEP chain (`AgeChain`) followed, extracted: given a member-index function
`d` and, for each `n`, potential embedding data `step n : A_{d n} → A_{d (n+1)}` that is an actual
embedding, the stages are the members totalized at uniformly extracted witnesses, the carrier steps
are the partial applications of the data, and the four step laws are read through one realizer
lemma. Totality enters only at the stage enumerations; the steps stay partial.

`EmbeddingChainData K` is proof-carrying by design: it is the *semantic* input of the assembly,
not a `Primcodable` datum. Nonemptiness propagates from the base member along the injective steps
(`domainAt_nonempty`), so only `(K.domainAt (d 0)).Nonempty` is asked.

**Transport identification** (`mem_transportTo_iff_applyPotentialPart`): the chain's carrier
transport from stage `r` to stage `r + k` is the application of any value of `foldData r k`, the
fold of `compPart` over the steps `r, …, r + k - 1` from the identity data at `r`. That fold is
what `transportPart` computes off a recorded prefix, so a chain assembled from a run inherits the
identification. Stated after assembly, as the contract requires; nothing in the assembly consumes
it.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

namespace PartialAgeIn

variable (K : PartialAgeIn O L)

/-- The semantic input of the assembly: a member-index function and actual connecting maps with
matching endpoints. -/
structure EmbeddingChainData where
  /-- The member at stage `n`. -/
  d : ℕ → ℕ
  /-- The connecting map from stage `n` to stage `n + 1`, as potential data. -/
  step : ℕ → PotentialEmbeddingData
  /-- It departs from the member at `n`. -/
  step_domIdx : ∀ n, (step n).domIdx = d n
  /-- It lands in the member at `n + 1`. -/
  step_codIdx : ∀ n, (step n).codIdx = d (n + 1)
  /-- It is an actual embedding. -/
  step_isEmbedding : ∀ n, K.PartialIsEmbedding (step n)

namespace EmbeddingChainData

variable {K}

/-! ### Endpoint bookkeeping, on plain naturals -/

theorem mem_step_domain (C : K.EmbeddingChainData) {n x : ℕ} (hx : x ∈ K.domainAt (C.d n)) :
    x ∈ (K.memberAt (C.step n).domIdx).domain := by
  rw [memberAt_domain, C.step_domIdx]; exact hx

theorem mem_domainAt_of_mem_step_codomain (C : K.EmbeddingChainData) {n y : ℕ}
    (hy : y ∈ (K.memberAt (C.step n).codIdx).domain) : y ∈ K.domainAt (C.d (n + 1)) := by
  rw [memberAt_domain, C.step_codIdx] at hy; exact hy

/-! ### Nonemptiness propagates -/

/-- An actual embedding out of a nonempty member lands in a nonempty member. -/
theorem domainAt_nonempty (C : K.EmbeddingChainData) (h0 : (K.domainAt (C.d 0)).Nonempty) (n : ℕ) :
    (K.domainAt (C.d n)).Nonempty := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    obtain ⟨x, hx⟩ := ih
    obtain ⟨f, -⟩ := C.step_isEmbedding n
    exact ⟨_, C.mem_domainAt_of_mem_step_codomain (f ⟨x, C.mem_step_domain hx⟩).2⟩

/-! ### The carrier steps -/

/-- The carrier step at transition `n`: the connecting data, applied. Partial. -/
noncomputable def chainStep (C : K.EmbeddingChainData) (n : ℕ) : ℕ →. ℕ :=
  fun x ↦ K.applyPotentialPart (C.step n) x

/-- **The one realizer lemma**: every accepted step value is the realizer's value. -/
theorem mem_chainStep_iff (C : K.EmbeddingChainData) {n : ℕ}
    {f : (K.memberAt (C.step n).domIdx).domain ↪[L] (K.memberAt (C.step n).codIdx).domain}
    (hf : K.PartialRealizes (C.step n) f) {x y : ℕ}
    (hx : x ∈ (K.memberAt (C.step n).domIdx).domain) :
    y ∈ C.chainStep n x ↔ y = ((f ⟨x, hx⟩ : (K.memberAt (C.step n).codIdx).domain) : ℕ) :=
  ⟨fun h ↦ Part.mem_unique h (applyPotentialPart_mem_realizer hf hx),
    fun h ↦ h ▸ applyPotentialPart_mem_realizer hf hx⟩

theorem chainStep_mem (C : K.EmbeddingChainData) (n x : ℕ) (hx : x ∈ K.domainAt (C.d n)) :
    ∃ y ∈ C.chainStep n x, y ∈ K.domainAt (C.d (n + 1)) := by
  obtain ⟨f, hf⟩ := C.step_isEmbedding n
  exact ⟨_, applyPotentialPart_mem_realizer hf (C.mem_step_domain hx),
    C.mem_domainAt_of_mem_step_codomain (f ⟨x, C.mem_step_domain hx⟩).2⟩

theorem chainStep_injOn (C : K.EmbeddingChainData) (n x₁ x₂ y : ℕ)
    (hx₁ : x₁ ∈ K.domainAt (C.d n)) (hx₂ : x₂ ∈ K.domainAt (C.d n))
    (h₁ : y ∈ C.chainStep n x₁) (h₂ : y ∈ C.chainStep n x₂) : x₁ = x₂ := by
  obtain ⟨f, hf⟩ := C.step_isEmbedding n
  rw [C.mem_chainStep_iff hf (C.mem_step_domain hx₁)] at h₁
  rw [C.mem_chainStep_iff hf (C.mem_step_domain hx₂)] at h₂
  have : f ⟨x₁, C.mem_step_domain hx₁⟩ = f ⟨x₂, C.mem_step_domain hx₂⟩ :=
    Subtype.ext (h₁ ▸ h₂ ▸ rfl)
  exact congrArg Subtype.val (f.injective this)

/-- Function preservation, at the data's own endpoints. -/
private theorem chainStep_funMap' (C : K.EmbeddingChainData) (n m : ℕ) (g : L.Functions m)
    (v w : Fin m → ℕ) (hv : ∀ k, v k ∈ (K.memberAt (C.step n).domIdx).domain)
    (hw : ∀ k, w k ∈ C.chainStep n (v k)) :
    @Structure.funMap L ℕ (K.structureAt (C.step n).codIdx) m g w ∈
      C.chainStep n (@Structure.funMap L ℕ (K.structureAt (C.step n).domIdx) m g v) := by
  obtain ⟨f, hf⟩ := C.step_isEmbedding n
  have hwv : w = fun k ↦ ((f ⟨v k, hv k⟩ : _) : ℕ) :=
    funext fun k ↦ (C.mem_chainStep_iff hf (hv k)).1 (hw k)
  have hclosed : @Structure.funMap L ℕ (K.structureAt (C.step n).domIdx) m g v ∈
      (K.memberAt (C.step n).domIdx).domain := K.domainAt_closed g hv
  subst hwv
  rw [C.mem_chainStep_iff hf hclosed]
  exact (congrArg Subtype.val (f.map_fun' g fun k ↦
    (⟨v k, hv k⟩ : (K.memberAt (C.step n).domIdx).domain))).symm

theorem chainStep_funMap (C : K.EmbeddingChainData) (n m : ℕ) (g : L.Functions m)
    (v w : Fin m → ℕ) (hv : ∀ k, v k ∈ K.domainAt (C.d n))
    (hw : ∀ k, w k ∈ C.chainStep n (v k)) :
    @Structure.funMap L ℕ (K.structureAt (C.d (n + 1))) m g w ∈
      C.chainStep n (@Structure.funMap L ℕ (K.structureAt (C.d n)) m g v) := by
  have h := C.chainStep_funMap' n m g v w (fun k ↦ C.mem_step_domain (hv k)) hw
  rwa [C.step_domIdx, C.step_codIdx] at h

/-- Relation preservation and reflection, at the data's own endpoints. -/
private theorem chainStep_relMap' (C : K.EmbeddingChainData) (n m : ℕ) (R : L.Relations m)
    (v w : Fin m → ℕ) (hv : ∀ k, v k ∈ (K.memberAt (C.step n).domIdx).domain)
    (hw : ∀ k, w k ∈ C.chainStep n (v k)) :
    (@Structure.RelMap L ℕ (K.structureAt (C.step n).codIdx) m R w ↔
      @Structure.RelMap L ℕ (K.structureAt (C.step n).domIdx) m R v) := by
  obtain ⟨f, hf⟩ := C.step_isEmbedding n
  have hwv : w = fun k ↦ ((f ⟨v k, hv k⟩ : _) : ℕ) :=
    funext fun k ↦ (C.mem_chainStep_iff hf (hv k)).1 (hw k)
  subst hwv
  exact f.map_rel' R fun k ↦ (⟨v k, hv k⟩ : (K.memberAt (C.step n).domIdx).domain)

theorem chainStep_relMap (C : K.EmbeddingChainData) (n m : ℕ) (R : L.Relations m)
    (v w : Fin m → ℕ) (hv : ∀ k, v k ∈ K.domainAt (C.d n))
    (hw : ∀ k, w k ∈ C.chainStep n (v k)) :
    (@Structure.RelMap L ℕ (K.structureAt (C.d (n + 1))) m R w ↔
      @Structure.RelMap L ℕ (K.structureAt (C.d n)) m R v) := by
  have h := C.chainStep_relMap' n m R v w (fun k ↦ C.mem_step_domain (hv k)) hw
  rwa [C.step_domIdx, C.step_codIdx] at h

/-! ### The totalized stages and the chain -/

/-- The `n`-th stage: the member at `d n`, totalized at its uniformly extracted witness, lifted to
the map oracle. -/
noncomputable def stage (C : K.EmbeddingChainData) (h0 : (K.domainAt (C.d 0)).Nonempty)
    (hOE : O ⊆ E) (n : ℕ) : CePresentationIn E L :=
  ((K.memberAt (C.d n)).toCePresentation
    (K.enum?_firstSomeStep C.d (C.domainAt_nonempty h0) n)).mono hOE

/-- **Totalizing did not move the carrier.** -/
theorem stage_domain (C : K.EmbeddingChainData) (h0 : (K.domainAt (C.d 0)).Nonempty)
    (hOE : O ⊆ E) (n : ℕ) : (C.stage h0 hOE n).domain = K.domainAt (C.d n) :=
  (K.memberAt (C.d n)).toCePresentation_domain
    (K.enum?_firstSomeStep C.d (C.domainAt_nonempty h0) n)

theorem stage_str (C : K.EmbeddingChainData) (h0 : (K.domainAt (C.d 0)).Nonempty)
    (hOE : O ⊆ E) (n : ℕ) : (C.stage h0 hOE n).str = K.structureAt (C.d n) := rfl

theorem stage_enum (C : K.EmbeddingChainData) (h0 : (K.domainAt (C.d 0)).Nonempty)
    (hOE : O ⊆ E) (n m : ℕ) :
    (C.stage h0 hOE n).enum m =
      (K.enum? (C.d n) m).getD (K.firstEnumeratedValue C.d (C.domainAt_nonempty h0) n) :=
  rfl

/-- Uniform computability of the stage enumerations, from computability of `d`. -/
theorem stage_enum_uniform (C : K.EmbeddingChainData) (h0 : (K.domainAt (C.d 0)).Nonempty)
    (hOE : O ⊆ E) (hd : ComputableIn E C.d) :
    ComputableIn E fun p : ℕ × ℕ ↦ (C.stage h0 hOE p.1).enum p.2 := by
  have henum : ComputableIn E fun p : ℕ × ℕ ↦ K.enum? (C.d p.1) p.2 :=
    (RecursiveIn.mono hOE K.enum?_computableIn).comp
      ((hd.comp ComputableIn.fst).pair ComputableIn.snd)
  have hwit : ComputableIn E fun p : ℕ × ℕ ↦
      K.firstEnumeratedValue C.d (C.domainAt_nonempty h0) p.1 :=
    (K.firstEnumeratedValue_computableIn C.d (C.domainAt_nonempty h0) hOE hd).comp
      ComputableIn.fst
  exact (ComputableIn.option_casesOn henum hwit ComputableIn.snd.to₂).of_eq fun p ↦ by
    rw [stage_enum]
    cases K.enum? (C.d p.1) p.2 <;> rfl

/-- **The assembled c.e. structure chain.** Stages are the totalized members; steps are the partial
applications of the connecting data. -/
noncomputable def toChain (C : K.EmbeddingChainData) (h0 : (K.domainAt (C.d 0)).Nonempty)
    (hOE : O ⊆ E) (hd : ComputableIn E C.d) (hstep : ComputableIn E C.step) :
    CeStructureChainIn E L where
  stageAt := C.stage h0 hOE
  enum_uniform := C.stage_enum_uniform h0 hOE hd
  step := C.chainStep
  step_recursiveIn :=
    RecursiveIn.comp (O := E) (α := ℕ × ℕ) (β := PotentialEmbeddingData × ℕ) (σ := ℕ)
      (f := fun q : PotentialEmbeddingData × ℕ ↦ K.applyPotentialPart q.1 q.2)
      (g := fun p : ℕ × ℕ ↦ (C.step p.1, p.2))
      (RecursiveIn.mono hOE K.applyPotentialPart_recursiveIn)
      ((hstep.comp ComputableIn.fst).pair ComputableIn.snd)
  step_mem := fun n x hx ↦ by
    rw [stage_domain] at hx
    simpa only [stage_domain] using C.chainStep_mem n x hx
  step_injOn := fun n x₁ x₂ y hx₁ hx₂ h₁ h₂ ↦ by
    rw [stage_domain] at hx₁ hx₂
    exact C.chainStep_injOn n x₁ x₂ y hx₁ hx₂ h₁ h₂
  step_funMap := fun n m g v w hv hw ↦ by
    simp only [stage_domain] at hv
    exact C.chainStep_funMap n m g v w hv hw
  step_relMap := fun n m R v w hv hw ↦ by
    simp only [stage_domain] at hv
    exact C.chainStep_relMap n m R v w hv hw

section Chain

variable (C : K.EmbeddingChainData) (h0 : (K.domainAt (C.d 0)).Nonempty) (hOE : O ⊆ E)
  (hd : ComputableIn E C.d) (hstep : ComputableIn E C.step)

@[simp] theorem toChain_stageAt (n : ℕ) :
    (C.toChain h0 hOE hd hstep).stageAt n = C.stage h0 hOE n := rfl

@[simp] theorem toChain_step : (C.toChain h0 hOE hd hstep).step = C.chainStep := rfl

theorem toChain_stage_domain (n : ℕ) :
    ((C.toChain h0 hOE hd hstep).stageAt n).domain = K.domainAt (C.d n) :=
  C.stage_domain h0 hOE n

/-- The chain's stage evaluators are uniformly partial recursive: they are the family's, read at
`d`. -/
theorem toChain_uniformEvaluators : (C.toChain h0 hOE hd hstep).UniformEvaluatorsIn where
  funEval_uniform :=
    ((RecursiveIn.mono hOE K.funEval_recursiveIn).comp
      ((hd.comp ComputableIn.fst).pair ComputableIn.snd)).of_eq fun _ ↦ rfl
  relEval_uniform :=
    ((RecursiveIn.mono hOE K.relEval_recursiveIn).comp
      ((hd.comp ComputableIn.fst).pair ComputableIn.snd)).of_eq fun _ ↦ rfl

end Chain

end EmbeddingChainData

/-! ### Application of composites and of the identity -/

variable {K}

/-- Application of a composite is the composite of the applications, on the source member. -/
theorem mem_applyPotentialPart_of_mem_compPart {G F H : PotentialEmbeddingData}
    (hFG : F.codIdx = G.domIdx) (hF : K.PartialIsEmbedding F) (hG : K.PartialIsEmbedding G)
    (hH : H ∈ K.compPart G F) {x y z : ℕ} (hx : x ∈ K.domainAt F.domIdx)
    (hy : y ∈ K.applyPotentialPart F x) (hz : z ∈ K.applyPotentialPart G y) :
    z ∈ K.applyPotentialPart H x := by
  obtain ⟨c, d, w⟩ := F
  obtain ⟨d', e, v⟩ := G
  cases hFG
  obtain ⟨f, hf⟩ := hF
  obtain ⟨g, hg⟩ := hG
  have hf' : K.PartialRealizes (PotentialEmbeddingData.ofTriple (c, d, w)) f := hf
  have hg' : K.PartialRealizes (PotentialEmbeddingData.ofTriple (d, e, v)) g := hg
  obtain ⟨v', hcomp, hreal⟩ := K.compPart_realizes hf' hg'
  have hH' : H ∈ K.compPart (PotentialEmbeddingData.ofTriple (d, e, v))
      (PotentialEmbeddingData.ofTriple (c, d, w)) := hH
  rw [hcomp, Part.mem_some_iff] at hH'
  subst hH'
  have hx' : x ∈ (K.memberAt c).domain := hx
  have hfx := applyPotentialPart_mem_realizer hf' hx'
  have hy' : y = ((f ⟨x, hx'⟩ : (K.memberAt d).domain) : ℕ) := Part.mem_unique hy hfx
  subst hy'
  have hgy := applyPotentialPart_mem_realizer hg' (f ⟨x, hx'⟩).2
  have hz' : z = ((g (f ⟨x, hx'⟩) : (K.memberAt e).domain) : ℕ) := Part.mem_unique hz hgy
  subst hz'
  exact applyPotentialPart_mem_realizer hreal hx'

/-- Application of the identity data is the identity, on the member. -/
theorem mem_applyPotentialPart_idData_iff {i x y : ℕ} (hx : x ∈ K.domainAt i) :
    y ∈ K.applyPotentialPart (K.idData i) x ↔ y = x :=
  ⟨fun h ↦ Part.mem_unique h (applyPotentialPart_mem_realizer (K.idData_realizes i) hx),
    fun h ↦ h ▸ applyPotentialPart_mem_realizer (K.idData_realizes i) hx⟩

namespace EmbeddingChainData

/-! ### Transport identification -/

/-- Folded transport data along the steps `r, …, r + k - 1`, from the identity data at `r`: the
semantic counterpart of `transportPart` on a recorded prefix. -/
noncomputable def foldData (C : K.EmbeddingChainData) (r : ℕ) : ℕ → Part PotentialEmbeddingData
  | 0 => Part.some (K.idData (C.d r))
  | k + 1 => (C.foldData r k).bind fun δ ↦ K.compPart (C.step (r + k)) δ

theorem foldData_zero (C : K.EmbeddingChainData) (r : ℕ) :
    C.foldData r 0 = Part.some (K.idData (C.d r)) := rfl

theorem foldData_succ (C : K.EmbeddingChainData) (r k : ℕ) :
    C.foldData r (k + 1) = (C.foldData r k).bind fun δ ↦ K.compPart (C.step (r + k)) δ := rfl

/-- Every value of the fold is an actual embedding from the member at `r` to the member at
`r + k`. -/
theorem foldData_partialIsEmbedding (C : K.EmbeddingChainData) (r : ℕ) :
    ∀ (k : ℕ) {δ : PotentialEmbeddingData}, δ ∈ C.foldData r k →
      δ.domIdx = C.d r ∧ δ.codIdx = C.d (r + k) ∧ K.PartialIsEmbedding δ
  | 0, δ, h => by
    rw [foldData_zero, Part.mem_some_iff] at h
    subst h
    exact ⟨rfl, rfl, K.idData_partialIsEmbedding _⟩
  | k + 1, δ, h => by
    rw [foldData_succ, Part.mem_bind_iff] at h
    obtain ⟨δ₀, h₀, hδ⟩ := h
    obtain ⟨hdom, hcod, hemb⟩ := C.foldData_partialIsEmbedding r k h₀
    have hFG : δ₀.codIdx = (C.step (r + k)).domIdx := by rw [hcod, C.step_domIdx]
    obtain ⟨H, hH, hHdom, hHcod, hHemb⟩ :=
      K.compPart_partialIsEmbedding hFG hemb (C.step_isEmbedding (r + k))
    obtain rfl := Part.mem_unique hH hδ
    refine ⟨hHdom.trans hdom, ?_, hHemb⟩
    rw [hHcod, C.step_codIdx, Nat.add_assoc]

/-- The fold halts at every length. -/
theorem foldData_dom (C : K.EmbeddingChainData) (r : ℕ) : ∀ k : ℕ, (C.foldData r k).Dom
  | 0 => trivial
  | k + 1 => by
    obtain ⟨δ, hδ⟩ := Part.dom_iff_mem.1 (C.foldData_dom r k)
    obtain ⟨-, hcod, hemb⟩ := C.foldData_partialIsEmbedding r k hδ
    have hFG : δ.codIdx = (C.step (r + k)).domIdx := by rw [hcod, C.step_domIdx]
    obtain ⟨H, hH, -, -, -⟩ := K.compPart_partialIsEmbedding hFG hemb (C.step_isEmbedding (r + k))
    exact Part.dom_iff_mem.2 ⟨H, by rw [foldData_succ]; exact Part.mem_bind_iff.2 ⟨δ, hδ, hH⟩⟩

/-- **Transport identification**: on a point of the member at `r`, the chain's transport from `r`
to `r + k` is the application of any value of the fold. -/
theorem mem_transportTo_iff_applyPotentialPart (C : K.EmbeddingChainData)
    (h0 : (K.domainAt (C.d 0)).Nonempty) (hOE : O ⊆ E) (hd : ComputableIn E C.d)
    (hstep : ComputableIn E C.step) (r : ℕ) :
    ∀ (k : ℕ) {δ : PotentialEmbeddingData}, δ ∈ C.foldData r k →
      ∀ {x y : ℕ}, x ∈ K.domainAt (C.d r) →
        (y ∈ (C.toChain h0 hOE hd hstep).transportTo r (r + k) x ↔
          y ∈ K.applyPotentialPart δ x)
  | 0, δ, hδ, x, y, hx => by
    rw [foldData_zero, Part.mem_some_iff] at hδ
    subst hδ
    rw [Nat.add_zero, CeStructureChainIn.transportTo, CeDomainChainIn.transportTo_self,
      Part.mem_some_iff, K.mem_applyPotentialPart_idData_iff hx]
  | k + 1, δ, hδ, x, y, hx => by
    rw [foldData_succ, Part.mem_bind_iff] at hδ
    obtain ⟨δ₀, h₀, hδ⟩ := hδ
    obtain ⟨hdom, hcod, hemb⟩ := C.foldData_partialIsEmbedding r k h₀
    have hFG : δ₀.codIdx = (C.step (r + k)).domIdx := by rw [hcod, C.step_domIdx]
    have hx' : x ∈ K.domainAt δ₀.domIdx := by rw [hdom]; exact hx
    have ih : ∀ {u : ℕ}, u ∈ (C.toChain h0 hOE hd hstep).transportTo r (r + k) x ↔
        u ∈ K.applyPotentialPart δ₀ x :=
      fun {u} ↦ C.mem_transportTo_iff_applyPotentialPart h0 hOE hd hstep r k h₀ (y := u) hx
    constructor
    · intro hy
      rw [← Nat.add_assoc] at hy
      obtain ⟨u, hu, hyu⟩ := (C.toChain h0 hOE hd hstep).transportTo_succ_right
        (Nat.le_add_right _ _) hy
      exact K.mem_applyPotentialPart_of_mem_compPart hFG hemb (C.step_isEmbedding (r + k)) hδ hx'
        (ih.1 hu) hyu
    · intro hy
      -- the transport halts on the member; its value is forced by the realizer
      obtain ⟨u, hu, -⟩ := (C.toChain h0 hOE hd hstep).toDomainChain.transportTo_dom (r + k)
        (Nat.le_add_right _ _)
        (by rw [CeStructureChainIn.toDomainChain_domainAt, toChain_stage_domain]; exact hx)
      have hu' := ih.1 hu
      have hu_mem : u ∈ K.domainAt (C.d (r + k)) := by
        have hland : ∀ z ∈ K.applyPotentialPart δ₀ x, z ∈ K.domainAt δ₀.codIdx := fun z hz ↦
          K.applyPotentialPart_mem_domainAt_of_partialIsEmbedding hemb hx' hz
        have := hland u hu'
        rwa [hcod] at this
      obtain ⟨w, hw, -⟩ := C.chainStep_mem (r + k) u hu_mem
      have hyw : y = w :=
        Part.mem_unique hy
          (K.mem_applyPotentialPart_of_mem_compPart hFG hemb (C.step_isEmbedding (r + k)) hδ hx'
            hu' hw)
      subst hyw
      rw [← Nat.add_assoc]
      exact (C.toChain h0 hOE hd hstep).toDomainChain.transportTo_trans (Nat.le_add_right _ _)
        (Nat.le_succ _) hu
        ((C.toChain h0 hOE hd hstep).toDomainChain.step_mem_transportTo_succ hw)

end EmbeddingChainData

end PartialAgeIn

end FirstOrder.Language
