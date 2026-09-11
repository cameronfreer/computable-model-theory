/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.ChainAssembly
import ComputableModelTheory.ModelTheory.Computable.ChainHistory

/-!
# A width-correct, `(n+1)`-correct candidate that is not an embedding

A shared fixture for the transition and run audits (an audit module cannot import another). On
the three-width successor family, `collapsingCandidate` is a requirement from `A_1` (two
generators) into
`A_2` (three generators) whose chain map sends both generators of `A_1` to the same point: it passes
both width equations and the `(n+1)` guard, is carrier-valid in every member, and is **not** an
embedding. It is the candidate the construction must still process — the transition must extend the
chain on it, and the scheduler must eventually select its code.

Also here: `identityChain`, the constant chain on member `0` with identity steps, the smallest
concrete input of the chain assembly, used by the assembly and exhaustion audits.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

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
theorem collapsingCandidate_staticAdmissible :
    (threeWidthFamily O).StaticAdmissible collapsingCandidate := by
  simp [PartialAgeIn.StaticAdmissible, collapsingCandidate, threeWidthFamily,
    ComputableAgeIn.toPartialAge, succAgeMixed]

/-- **Carrier-valid** in any member (the lifted family has full carriers). -/
theorem collapsingCandidate_carrierValid (d : ℕ → ℕ) :
    (threeWidthFamily O).CarrierValid (collapsingCandidate.chainMap d) ∧
      (threeWidthFamily O).CarrierValid collapsingCandidate.targetMap :=
  ⟨fun _ _ ↦ by simp [threeWidthFamily], fun _ _ ↦ by simp [threeWidthFamily]⟩

/-- **Not an embedding**: both generators of `A_1` go to `0`, but an embedding is injective and the
generators `0` and `1` of `A_1` are distinct. -/
theorem collapsingCandidate_not_partialIsEmbedding (d : ℕ → ℕ) :
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


/-! ### The identity chain -/

/-- The constant chain on member `0` with identity steps. -/
noncomputable def identityChain : (threeWidthFamily O).EmbeddingChainData where
  d := fun _ ↦ 0
  step := fun _ ↦ (threeWidthFamily O).idData 0
  step_domIdx := fun _ ↦ rfl
  step_codIdx := fun _ ↦ rfl
  step_isEmbedding := fun _ ↦ (threeWidthFamily O).idData_partialIsEmbedding 0

theorem identityChain_nonempty :
    ((threeWidthFamily O).domainAt ((identityChain O).d 0)).Nonempty :=
  ⟨0, by simp [threeWidthFamily]⟩

end FirstOrder.Language
