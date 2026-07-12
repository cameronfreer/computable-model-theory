/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.UniformAtomic
import ComputableModelTheory.ModelTheory.Computable.PotentialEmbedding

/-!
# Uniform nonembedding witnesses and embedding information

The failure of actualness of arbitrary potential embedding data over a computable age
is r.e. in the oracle, uniformly in the data. A disagreement witness
(`AtomicDisagreement`) is well-formedness together with atomic data — valid at the
domain generator width — realized differently at the domain and codomain; it is
computable uniformly in the data and the witness. A single tagged natural-number
search (`nonEmbeddingCandidate`: candidate `0` is malformedness, candidate `n + 1`
decodes `n` as disagreeing valid data) avoids r.e. disjunction and dovetailing, and
characterizes non-actualness exactly through the central semantic bridge.

`EmbeddingInformation` is defined purely semantically as the set of actual data; its
complement is r.e. in the oracle. No characteristic oracle is defined here — actualness
is not decidable at this stage; the jump layer will later turn the r.e. complement
into a decision procedure.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

namespace ComputableAgeIn

variable (K : ComputableAgeIn O L)

/-- Well-formedness of potential embedding data is computable uniformly in the
data. -/
theorem wellFormed_computablePredIn :
    ComputablePredIn O fun F : PotentialEmbeddingData ↦ F.WellFormed K := by
  refine ⟨fun F ↦ instDecidableEqNat _ _, ?_⟩
  have hB : ComputableIn O fun F : PotentialEmbeddingData ↦
      decide (F.rangeTuple.length = (K.gens F.domIdx).length) :=
    (Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂.comp
      ((Primrec.list_length.comp
        PotentialEmbeddingData.primrec_rangeTuple).to_comp.computableIn)
      ((Primrec.list_length.to_comp.computableIn).comp
        (K.gens_computableIn.comp
          (PotentialEmbeddingData.primrec_domIdx.to_comp.computableIn)))
  exact hB.of_eq fun F ↦ decide_eq_decide.2 Iff.rfl

/-- An atomic disagreement witness: well-formed data together with atomic data, valid
at the domain generator width, realized differently at the domain and the codomain. -/
def AtomicDisagreement (F : PotentialEmbeddingData) (d : AtomicData L ℕ) : Prop :=
  F.WellFormed K ∧ AtomicData.ValidAt (K.gens F.domIdx).length d ∧
    ¬(K.realizeAtomicData F.domIdx (K.gens F.domIdx) d ↔
      K.realizeAtomicData F.codIdx F.rangeTuple d)

set_option maxHeartbeats 1000000 in
/-- Atomic disagreement is computable uniformly in the data and the witness. -/
theorem atomicDisagreement_computablePredIn :
    ComputablePredIn O fun p : PotentialEmbeddingData × AtomicData L ℕ ↦
      K.AtomicDisagreement p.1 p.2 := by
  have hWF : ComputablePredIn O
      fun p : PotentialEmbeddingData × AtomicData L ℕ ↦ p.1.WellFormed K :=
    (K.wellFormed_computablePredIn).comp ComputableIn.fst
  have hValid : ComputablePredIn O
      fun p : PotentialEmbeddingData × AtomicData L ℕ ↦
      AtomicData.ValidAt (K.gens p.1.domIdx).length p.2 := by
    refine ⟨fun p ↦ decidable_of_iff _ (AtomicData.validAtBool_iff _ _), ?_⟩
    have hB : ComputableIn O fun p : PotentialEmbeddingData × AtomicData L ℕ ↦
        AtomicData.validAtBool (K.gens p.1.domIdx).length p.2 :=
      (AtomicData.primrec₂_validAtBool.to_comp.computableIn₂).comp
        ((Primrec.list_length.to_comp.computableIn).comp
          (K.gens_computableIn.comp
            ((PotentialEmbeddingData.primrec_domIdx.to_comp.computableIn).comp
              ComputableIn.fst)))
        ComputableIn.snd
    exact hB.of_eq fun p ↦
      (Bool.decide_coe _).symm.trans
        (decide_eq_decide.2 (AtomicData.validAtBool_iff _ _))
  have hRdom : ComputablePredIn O
      fun p : PotentialEmbeddingData × AtomicData L ℕ ↦
      K.realizeAtomicData p.1.domIdx (K.gens p.1.domIdx) p.2 :=
    (K.realizeAtomicData_computablePredIn).comp
      ((((PotentialEmbeddingData.primrec_domIdx.to_comp.computableIn).comp
        ComputableIn.fst).pair
        (K.gens_computableIn.comp
          ((PotentialEmbeddingData.primrec_domIdx.to_comp.computableIn).comp
            ComputableIn.fst))).pair ComputableIn.snd)
  have hRcod : ComputablePredIn O
      fun p : PotentialEmbeddingData × AtomicData L ℕ ↦
      K.realizeAtomicData p.1.codIdx p.1.rangeTuple p.2 :=
    (K.realizeAtomicData_computablePredIn).comp
      ((((PotentialEmbeddingData.primrec_codIdx.to_comp.computableIn).comp
        ComputableIn.fst).pair
        ((PotentialEmbeddingData.primrec_rangeTuple.to_comp.computableIn).comp
          ComputableIn.fst)).pair ComputableIn.snd)
  exact (hWF.and (hValid.and (hRdom.iff hRcod).not)).of_eq fun p ↦ Iff.rfl

/-- The tagged search predicate: candidate `0` is malformedness; candidate `n + 1`
decodes `n` as disagreeing valid atomic data. -/
def nonEmbeddingCandidate (F : PotentialEmbeddingData) : ℕ → Prop
  | 0 => ¬F.WellFormed K
  | n + 1 =>
    Option.casesOn (motive := fun _ ↦ Prop)
      (@decode (AtomicData L ℕ) Primcodable.toEncodable n) False
      fun d ↦ K.AtomicDisagreement F d

/-- Every disagreement witness supplies a candidate, independently of coding. -/
theorem exists_nonEmbeddingCandidate_of_atomicDisagreement
    {F : PotentialEmbeddingData} {d : AtomicData L ℕ}
    (hd : K.AtomicDisagreement F d) : ∃ n, K.nonEmbeddingCandidate F n := by
  refine ⟨@encode (AtomicData L ℕ) Primcodable.toEncodable d + 1, ?_⟩
  show Option.casesOn (motive := fun _ ↦ Prop)
    (@decode (AtomicData L ℕ) Primcodable.toEncodable
      (@encode (AtomicData L ℕ) Primcodable.toEncodable d)) False
    (fun d ↦ K.AtomicDisagreement F d)
  rw [@encodek (AtomicData L ℕ) Primcodable.toEncodable d]
  exact hd

/-- The search characterizes non-actualness. -/
theorem exists_nonEmbeddingCandidate_iff (F : PotentialEmbeddingData) :
    (∃ n, K.nonEmbeddingCandidate F n) ↔ ¬F.IsEmbedding K := by
  constructor
  · rintro ⟨n, hn⟩
    match n, hn with
    | 0, hn => exact PotentialEmbeddingData.not_isEmbedding_of_not_wellFormed hn
    | n + 1, hn =>
      have hn' : Option.casesOn (motive := fun _ ↦ Prop)
          (@decode (AtomicData L ℕ) Primcodable.toEncodable n) False
          (fun d ↦ K.AtomicDisagreement F d) := hn
      rcases hd : @decode (AtomicData L ℕ) Primcodable.toEncodable n with - | d
      · rw [hd] at hn'
        exact hn'.elim
      · rw [hd] at hn'
        obtain ⟨hWF, hValid, hNe⟩ := hn'
        rintro ⟨h, hAE⟩
        exact hNe (((K.atomicEquivalent_iff_forall_validAtomicData F.domIdx F.codIdx
          (K.gens F.domIdx) F.rangeTuple h).1 hAE) d hValid)
  · intro hne
    by_cases hWF : F.WellFormed K
    · have hAE' : ¬@AtomicEquivalent L ℕ ℕ (K.structureAt F.domIdx)
          (K.structureAt F.codIdx) _ (K.gens F.domIdx).view
          (fun x ↦ F.rangeTuple.view (Fin.cast hWF.symm x)) :=
        fun hAE ↦ hne ⟨hWF, hAE⟩
      rw [K.atomicEquivalent_iff_forall_validAtomicData F.domIdx F.codIdx
        (K.gens F.domIdx) F.rangeTuple hWF] at hAE'
      obtain ⟨d, hd⟩ := not_forall.1 hAE'
      obtain ⟨hv, hni⟩ := Classical.not_imp.1 hd
      exact K.exists_nonEmbeddingCandidate_of_atomicDisagreement ⟨hWF, hv, hni⟩
    · exact ⟨0, hWF⟩

set_option maxHeartbeats 1000000 in
/-- The tagged search predicate is computable uniformly in the data and the tag. -/
theorem nonEmbeddingCandidate_computablePredIn :
    ComputablePredIn O fun p : PotentialEmbeddingData × ℕ ↦
      K.nonEmbeddingCandidate p.1 p.2 := by
  obtain ⟨hWdec, hWcomp⟩ := K.wellFormed_computablePredIn
  obtain ⟨hDdec, hDcomp⟩ := K.atomicDisagreement_computablePredIn
  refine ⟨fun p ↦ ?_, ?_⟩
  · rcases p with ⟨F, - | n⟩
    · exact @instDecidableNot _ (hWdec F)
    · exact Option.rec
        (motive := fun o ↦ Decidable (Option.casesOn (motive := fun _ ↦ Prop) o
          False fun d ↦ K.AtomicDisagreement F d))
        (inferInstanceAs (Decidable False)) (fun d ↦ hDdec (F, d))
        (@decode (AtomicData L ℕ) Primcodable.toEncodable n)
  · have hB : ComputableIn O fun p : PotentialEmbeddingData × ℕ ↦
        Nat.casesOn (motive := fun _ ↦ Bool) p.2 (!(decide (p.1.WellFormed K)))
          fun n ↦ Option.casesOn (motive := fun _ ↦ Bool)
            (@decode (AtomicData L ℕ) Primcodable.toEncodable n) false
            fun d ↦ decide ((fun q : PotentialEmbeddingData × AtomicData L ℕ ↦
              K.AtomicDisagreement q.1 q.2) (p.1, d)) :=
      ComputableIn.nat_casesOn ComputableIn.snd
        ((Primrec.not.to_comp.computableIn).comp (hWcomp.comp ComputableIn.fst))
        ((ComputableIn.option_casesOn
          ((Computable.decode.computableIn).comp ComputableIn.snd)
          (ComputableIn.const false)
          ((hDcomp.comp
            ((ComputableIn.fst.comp (ComputableIn.fst.comp ComputableIn.fst)).pair
              ComputableIn.snd)).to₂)).to₂)
    have hbridge : ∀ (F : PotentialEmbeddingData) (o : Option (AtomicData L ℕ)),
        (Option.casesOn (motive := fun _ ↦ Bool) o false fun d ↦
          decide ((fun q : PotentialEmbeddingData × AtomicData L ℕ ↦
            K.AtomicDisagreement q.1 q.2) (F, d))) =
        @decide (Option.casesOn (motive := fun _ ↦ Prop) o False
            fun d ↦ K.AtomicDisagreement F d)
          (Option.rec (inferInstanceAs (Decidable False))
            (fun d ↦ hDdec (F, d)) o) := by
      rintro F (- | d)
      · exact (decide_eq_false fun h ↦ h).symm
      · exact decide_eq_decide.2 Iff.rfl
    refine hB.of_eq fun p ↦ ?_
    rcases p with ⟨F, - | n⟩
    · by_cases hw : F.WellFormed K <;> simp [nonEmbeddingCandidate, hw]
    · exact hbridge F _

/-- Non-actualness of arbitrary potential embedding data is r.e. in the oracle,
uniformly in the data. -/
theorem not_isEmbedding_rePredIn :
    REPredIn O fun F : PotentialEmbeddingData ↦ ¬F.IsEmbedding K :=
  (REPredIn.exists_nat_of_computablePredIn
    (p := fun F n ↦ K.nonEmbeddingCandidate F n)
    (K.nonEmbeddingCandidate_computablePredIn)).of_eq
    fun F ↦ K.exists_nonEmbeddingCandidate_iff F

end ComputableAgeIn

/-- Semantic embedding information: the set of actual potential embedding data over a
computable age. No characteristic oracle is defined here — actualness is not decidable
at this stage. -/
def EmbeddingInformation (K : ComputableAgeIn O L) : Set PotentialEmbeddingData :=
  { F | F.IsEmbedding K }

/-- The complement of embedding information is r.e. in the oracle. -/
theorem embeddingInformation_compl_rePredIn (K : ComputableAgeIn O L) :
    REPredIn O fun F : PotentialEmbeddingData ↦ F ∈ (EmbeddingInformation K)ᶜ :=
  (K.not_isEmbedding_rePredIn).of_eq fun _ ↦ Iff.rfl

end FirstOrder.Language
