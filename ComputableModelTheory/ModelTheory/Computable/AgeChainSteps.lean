/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.AgeChainSchedule
import ComputableModelTheory.ModelTheory.Computable.PartialPotentialTransport

/-!
# The chain steps of a CJEP schedule

The scheduled left legs, turned into carrier maps. `CeStructureChainIn.step` is `Part`-valued, so
nothing here needs totalizing: `applyPotentialPart` stays partial, and only the *stage
presentations* are totalized — by the witness extraction of `AgeChainWitness`, which is a different
job on different data.

The four step laws are not four searches through `applyPotentialPart`. They all come from one
lemma, `mem_chainStep_iff`, which identifies every accepted step value with the value of an
explicitly supplied realizer. Once that is in hand, injectivity is the embedding's injectivity and
the two structure laws are its `map_fun'` and `map_rel'` — semantic applications of a bundled
embedding rather than reasoning about a partial machine. All `Part.mem_unique` traffic is absorbed
into that one lemma.

**The oracle boundary.** The application machine is recursive in the *presentation* oracle `O`,
while the schedule and the joint-embedding data are computable in the *map* oracle `E` of the CJEP
selector. Composing them is what forces `O ⊆ E`, and the resulting chain lives at `E`.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

namespace PartialAgeIn

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable {K : PartialAgeIn O L} {sel : ℕ → ℕ → PartialJointEmbeddingData} {baseIdx : ℕ}

/-! ### The scheduled data is computable -/

theorem stepData_computableIn (hsel : ComputableIn E fun p : ℕ × ℕ ↦ sel p.1 p.2) :
    ComputableIn E (stepData sel baseIdx) := by
  have hd : ComputableIn E (cjepSchedule sel baseIdx) := cjepSchedule_computableIn sel baseIdx hsel
  have hsucc : ComputableIn E fun n ↦ cjepSchedule sel baseIdx (n + 1) :=
    hd.comp (Primrec.succ.to_comp.computableIn)
  have hleft : ComputableIn E fun n ↦ (sel (cjepSchedule sel baseIdx n) n).leftImage :=
    (PartialJointEmbeddingData.primrec_leftImage.to_comp.computableIn).comp
      (hsel.comp (hd.pair ComputableIn.id))
  exact (PotentialEmbeddingData.primrec_ofTriple.to_comp.computableIn).comp
    (hd.pair (hsucc.pair hleft))

theorem cofinalData_computableIn (hsel : ComputableIn E fun p : ℕ × ℕ ↦ sel p.1 p.2) :
    ComputableIn E (cofinalData sel baseIdx) := by
  have hd : ComputableIn E (cjepSchedule sel baseIdx) := cjepSchedule_computableIn sel baseIdx hsel
  have hsucc : ComputableIn E fun n ↦ cjepSchedule sel baseIdx (n + 1) :=
    hd.comp (Primrec.succ.to_comp.computableIn)
  have hright : ComputableIn E fun n ↦ (sel (cjepSchedule sel baseIdx n) n).rightImage :=
    (PartialJointEmbeddingData.primrec_rightImage.to_comp.computableIn).comp
      (hsel.comp (hd.pair ComputableIn.id))
  exact (PotentialEmbeddingData.primrec_ofTriple.to_comp.computableIn).comp
    (ComputableIn.id.pair (hsucc.pair hright))

/-! ### The step maps -/

/-- The chain step at transition `n`: the left leg, applied to a carrier element. Partial, as
`CeStructureChainIn.step` is — no totalization is wanted or needed here. -/
noncomputable def chainStep (K : PartialAgeIn O L) (sel : ℕ → ℕ → PartialJointEmbeddingData)
    (baseIdx n : ℕ) : ℕ →. ℕ :=
  fun x ↦ K.applyPotentialPart (stepData sel baseIdx n) x

/-- **The one realizer lemma.** Every accepted step value *is* the supplied realizer's value.
Everything below is a semantic application of the bundled embedding; no other statement reasons
about the partial machine. -/
theorem mem_chainStep_iff {n : ℕ}
    {f : (K.memberAt (stepData sel baseIdx n).domIdx).domain ↪[L]
      (K.memberAt (stepData sel baseIdx n).codIdx).domain}
    (hf : K.PartialRealizes (stepData sel baseIdx n) f) {x y : ℕ}
    (hx : x ∈ (K.memberAt (stepData sel baseIdx n).domIdx).domain) :
    y ∈ chainStep K sel baseIdx n x ↔
      y = ((f ⟨x, hx⟩ : (K.memberAt (stepData sel baseIdx n).codIdx).domain) : ℕ) := by
  constructor
  · exact fun h ↦ Part.mem_unique h (applyPotentialPart_mem_realizer hf hx)
  · rintro rfl
    exact applyPotentialPart_mem_realizer hf hx

/-! ### The four step laws

Each is the corresponding property of the realizer, read through `mem_chainStep_iff`. -/

theorem chainStep_mem (hspec : K.JointSpec sel) (n x : ℕ)
    (hx : x ∈ K.domainAt (cjepSchedule sel baseIdx n)) :
    ∃ y ∈ chainStep K sel baseIdx n x, y ∈ K.domainAt (cjepSchedule sel baseIdx (n + 1)) := by
  obtain ⟨f, hf⟩ := stepData_partialIsEmbedding (baseIdx := baseIdx) hspec n
  exact ⟨_, applyPotentialPart_mem_realizer hf hx, (f ⟨x, hx⟩).2⟩

theorem chainStep_injOn (hspec : K.JointSpec sel) (n x₁ x₂ y : ℕ)
    (hx₁ : x₁ ∈ K.domainAt (cjepSchedule sel baseIdx n))
    (hx₂ : x₂ ∈ K.domainAt (cjepSchedule sel baseIdx n))
    (h₁ : y ∈ chainStep K sel baseIdx n x₁) (h₂ : y ∈ chainStep K sel baseIdx n x₂) : x₁ = x₂ := by
  obtain ⟨f, hf⟩ := stepData_partialIsEmbedding (baseIdx := baseIdx) hspec n
  rw [mem_chainStep_iff hf hx₁] at h₁
  rw [mem_chainStep_iff hf hx₂] at h₂
  have : f ⟨x₁, hx₁⟩ = f ⟨x₂, hx₂⟩ := Subtype.ext (h₁ ▸ h₂ ▸ rfl)
  exact congrArg Subtype.val (f.injective this)

theorem chainStep_funMap (hspec : K.JointSpec sel) (n m : ℕ) (g : L.Functions m)
    (v w : Fin m → ℕ) (hv : ∀ k, v k ∈ K.domainAt (cjepSchedule sel baseIdx n))
    (hw : ∀ k, w k ∈ chainStep K sel baseIdx n (v k)) :
    @Structure.funMap L ℕ (K.structureAt (cjepSchedule sel baseIdx (n + 1))) m g w ∈
      chainStep K sel baseIdx n
        (@Structure.funMap L ℕ (K.structureAt (cjepSchedule sel baseIdx n)) m g v) := by
  obtain ⟨f, hf⟩ := stepData_partialIsEmbedding (baseIdx := baseIdx) hspec n
  have hv' : ∀ k, v k ∈ (K.memberAt (stepData sel baseIdx n).domIdx).domain := hv
  have hwv : w = fun k ↦ ((f ⟨v k, hv' k⟩ : _) : ℕ) :=
    funext fun k ↦ (mem_chainStep_iff hf (hv' k)).1 (hw k)
  have hclosed : @Structure.funMap L ℕ (K.structureAt (cjepSchedule sel baseIdx n)) m g v ∈
      (K.memberAt (stepData sel baseIdx n).domIdx).domain := K.domainAt_closed g hv
  subst hwv
  rw [mem_chainStep_iff hf hclosed]
  exact (congrArg Subtype.val (f.map_fun' g fun k ↦
    (⟨v k, hv' k⟩ : (K.memberAt (stepData sel baseIdx n).domIdx).domain))).symm

theorem chainStep_relMap (hspec : K.JointSpec sel) (n m : ℕ) (R : L.Relations m)
    (v w : Fin m → ℕ) (hv : ∀ k, v k ∈ K.domainAt (cjepSchedule sel baseIdx n))
    (hw : ∀ k, w k ∈ chainStep K sel baseIdx n (v k)) :
    (@Structure.RelMap L ℕ (K.structureAt (cjepSchedule sel baseIdx (n + 1))) m R w ↔
      @Structure.RelMap L ℕ (K.structureAt (cjepSchedule sel baseIdx n)) m R v) := by
  obtain ⟨f, hf⟩ := stepData_partialIsEmbedding (baseIdx := baseIdx) hspec n
  have hv' : ∀ k, v k ∈ (K.memberAt (stepData sel baseIdx n).domIdx).domain := hv
  have hwv : w = fun k ↦ ((f ⟨v k, hv' k⟩ : _) : ℕ) :=
    funext fun k ↦ (mem_chainStep_iff hf (hv' k)).1 (hw k)
  subst hwv
  exact f.map_rel' R fun k ↦
    (⟨v k, hv' k⟩ : (K.memberAt (stepData sel baseIdx n).domIdx).domain)

end PartialAgeIn

end FirstOrder.Language
