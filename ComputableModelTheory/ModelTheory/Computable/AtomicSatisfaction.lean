/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.TermEvaluation
import ComputableModelTheory.ModelTheory.Syntax.Complexity

/-!
# Computable atomic satisfaction

The roadmap PR 7 second half: in an ω-presented computable structure, satisfaction of
atomic formulas is a computable predicate. The decider dispatches on the nondependent
atomic data extracted by `atomicData?`: an equality is decided by evaluating both terms
through computable term evaluation and comparing; a relation is decided by evaluating
the argument-term list, packaging the values as uniform relation application data, and
calling the structure's uniform relation decider.

Three public forms: the diagram-ready total predicate
`atomic_realize_computablePredIn` (atomicity together with satisfaction, deciding
`false` off the atomic fragment — the bridge to atomic diagrams), the uniform subtype
form `atomicFormula_realize_computablePredIn`, and the pointwise corollary
`realize_computablePredIn_of_isAtomic` for a fixed atomic formula.
-/

open Encodable FirstOrder Language Language.BoundedFormula

namespace FirstOrder.Language

variable {L : Language}

section AtomicSatisfaction

variable [L.EffectiveLanguage] [L.Structure ℕ] {k : ℕ}

omit [L.EffectiveLanguage] in
private theorem realize_relabelElim (t : L.Term (Fin k ⊕ Fin 0)) (v : Fin k → ℕ)
    (xs : Fin 0 → ℕ) :
    (t.relabel (Sum.elim id Fin.elim0)).realize v = t.realize (Sum.elim v xs) := by
  rw [Term.realize_relabel]
  congr 1
  funext i
  rcases i with i | i
  · rfl
  · exact i.elim0

open Classical in
/-- The atomic-satisfaction decider: dispatch on the extracted atomic data, deciding
`false` off the atomic fragment. -/
noncomputable def atomicSatBool (p : L.Formula (Fin k) × (Fin k → ℕ)) : Bool :=
  Option.casesOn (motive := fun _ ↦ Bool) (atomicData? p.1) false fun d ↦
    Sum.casesOn (motive := fun _ ↦ Bool) d
      (fun q ↦ decide (q.1.realize p.2 = q.2.realize p.2))
      fun q ↦
        Option.casesOn (motive := fun _ ↦ Bool)
          (RelationApplicationData.ofSymbolArgs?
            (q.1, q.2.map fun t ↦ t.realize p.2)) false
          fun d ↦ decide d.relMap

omit [L.EffectiveLanguage] [L.Structure ℕ] in
private theorem atomicData?_eq_none_of_not_isAtomic {φ : L.Formula (Fin k)}
    (h : ¬(φ : L.BoundedFormula (Fin k) 0).IsAtomic) : atomicData? φ = none :=
  Option.not_isSome_iff_eq_none.1 fun hs ↦ h ((atomicData?_isSome_iff φ).1 hs)

omit [L.EffectiveLanguage] in
open Classical in
/-- The decider decides atomicity together with satisfaction. -/
theorem atomicSatBool_iff (p : L.Formula (Fin k) × (Fin k → ℕ)) :
    atomicSatBool p = true ↔
      ((p.1 : L.BoundedFormula (Fin k) 0).IsAtomic ∧ p.1.Realize p.2) := by
  rcases p with ⟨φ, v⟩
  dsimp only
  cases φ with
  | falsum =>
    rw [atomicSatBool, atomicData?_eq_none_of_not_isAtomic (by rintro ⟨⟩)]
    refine iff_of_false (by simp) fun h ↦ ?_
    exact absurd h.1 (by rintro ⟨⟩)
  | imp φ₁ φ₂ =>
    rw [atomicSatBool, atomicData?_eq_none_of_not_isAtomic (fun h ↦ by cases h)]
    refine iff_of_false (by simp) fun h ↦ ?_
    exact absurd h.1 (fun h' ↦ by cases h')
  | all φ =>
    rw [atomicSatBool, atomicData?_eq_none_of_not_isAtomic (fun h ↦ by cases h)]
    refine iff_of_false (by simp) fun h ↦ ?_
    exact absurd h.1 (fun h' ↦ by cases h')
  | equal t₁ t₂ =>
    rw [atomicSatBool, atomicData?_eq_some_of_equal]
    show decide _ = true ↔ _
    rw [decide_eq_true_iff]
    constructor
    · intro h
      refine ⟨IsAtomic.equal t₁ t₂, ?_⟩
      rw [Formula.Realize]
      refine (BoundedFormula.realize_bdEqual t₁ t₂).2 ?_
      rw [← realize_relabelElim t₁ v, ← realize_relabelElim t₂ v]
      exact h
    · rintro ⟨-, h⟩
      rw [Formula.Realize] at h
      have h2 := (BoundedFormula.realize_bdEqual t₁ t₂).1 h
      rw [← realize_relabelElim t₁ v, ← realize_relabelElim t₂ v] at h2
      exact h2
  | rel R ts =>
    rw [atomicSatBool, atomicData?_eq_some_of_rel]
    show (Option.casesOn (motive := fun _ ↦ Bool)
      (RelationApplicationData.ofSymbolArgs? (_, _)) false fun d ↦ decide d.relMap) =
        true ↔ _
    rw [RelationApplicationData.ofSymbolArgs?_of_length_eq _ (by
      simp [RelationSymbol.arity])]
    show decide _ = true ↔ _
    rw [decide_eq_true_iff, RelationApplicationData.relMap_equivSubtype_symm]
    constructor
    · intro h
      refine ⟨IsAtomic.rel R ts, ?_⟩
      rw [Formula.Realize]
      refine BoundedFormula.realize_rel.2 ?_
      convert h using 2
      rw [List.get_eq_getElem, List.getElem_map, List.getElem_map,
        List.getElem_finRange]
      exact (realize_relabelElim _ v _).symm
    · rintro ⟨-, h⟩
      rw [Formula.Realize] at h
      have h' := BoundedFormula.realize_rel.1 h
      convert h' using 2
      rw [List.get_eq_getElem, List.getElem_map, List.getElem_map,
        List.getElem_finRange]
      exact realize_relabelElim _ v _

set_option maxHeartbeats 4000000 in
private theorem computableIn_atomicSatAux (O : Set (ℕ →. ℕ))
    [IsComputableStructureIn O L] (k : ℕ)
    (hdec : DecidablePred (RelationApplicationData.relMap (L := L) (M := ℕ)))
    (hcomp : ComputableIn O fun d : RelationApplicationData L ℕ ↦ @decide _ (hdec d)) :
    ComputableIn O fun p : L.Formula (Fin k) × (Fin k → ℕ) ↦
      Option.casesOn (motive := fun _ ↦ Bool) (atomicData? p.1) false fun d ↦
        Sum.casesOn (motive := fun _ ↦ Bool) d
          (fun q ↦ decide (q.1.realize p.2 = q.2.realize p.2))
          fun q ↦
            Option.casesOn (motive := fun _ ↦ Bool)
              (RelationApplicationData.ofSymbolArgs?
                (q.1, q.2.map fun t ↦ t.realize p.2)) false
              fun d ↦ @decide _ (hdec d) := by
  have hval : ComputableIn O fun q : ((L.Formula (Fin k) × (Fin k → ℕ)) ×
      AtomicData L (Fin k)) × L.Term (Fin k) ↦ q.2.realize q.1.1.2 :=
    (Term.realize_computableIn O (m := k)).comp
      (ComputableIn.snd.pair
        ((Computable.snd.computableIn).comp
          ((Computable.fst.computableIn).comp ComputableIn.fst)))
  have hEq : ComputableIn₂ O fun (x : (L.Formula (Fin k) × (Fin k → ℕ)) ×
      AtomicData L (Fin k)) (q : L.Term (Fin k) × L.Term (Fin k)) ↦
      decide (q.1.realize x.1.2 = q.2.realize x.1.2) :=
    ((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂.comp
      (hval.comp (ComputableIn.fst.pair
        (Computable.fst.computableIn.comp ComputableIn.snd)))
      (hval.comp (ComputableIn.fst.pair
        (Computable.snd.computableIn.comp ComputableIn.snd)))).to₂
  have hRel : ComputableIn₂ O fun (x : (L.Formula (Fin k) × (Fin k → ℕ)) ×
      AtomicData L (Fin k)) (q : L.RelationSymbol × List (L.Term (Fin k))) ↦
      Option.casesOn (motive := fun _ ↦ Bool)
        (RelationApplicationData.ofSymbolArgs?
          (q.1, q.2.map fun t ↦ t.realize x.1.2)) false
        fun d ↦ @decide _ (hdec d) := by
    have hvals : ComputableIn O fun y : ((L.Formula (Fin k) × (Fin k → ℕ)) ×
        AtomicData L (Fin k)) × L.RelationSymbol × List (L.Term (Fin k)) ↦
        y.2.2.map fun t ↦ t.realize y.1.1.2 :=
      ComputableIn.list_map
        ((Computable.snd.computableIn).comp ComputableIn.snd)
        (((Term.realize_computableIn O (m := k)).comp
          (ComputableIn.snd.pair
            ((Computable.snd.computableIn).comp
              ((Computable.fst.computableIn).comp
                (ComputableIn.fst.comp ComputableIn.fst))))).to₂)
    have hofs : ComputableIn O fun y : ((L.Formula (Fin k) × (Fin k → ℕ)) ×
        AtomicData L (Fin k)) × L.RelationSymbol × List (L.Term (Fin k)) ↦
        RelationApplicationData.ofSymbolArgs?
          (y.2.1, y.2.2.map fun t ↦ t.realize y.1.1.2) :=
      (RelationApplicationData.primrec_ofSymbolArgs?.to_comp.computableIn).comp
        (((Computable.fst.computableIn).comp ComputableIn.snd).pair hvals)
    exact (ComputableIn.option_casesOn hofs (ComputableIn.const false)
      ((hcomp.comp ComputableIn.snd).to₂)).to₂
  exact ComputableIn.option_casesOn
    ((primrec_atomicData?.to_comp.computableIn).comp
      (Computable.fst.computableIn))
    (ComputableIn.const false)
    ((ComputableIn.sumCasesOn ComputableIn.snd hEq hRel).to₂)

/-- The roadmap PR 7 gate in diagram-ready total form: atomicity together with
satisfaction is a computable predicate on formulas with tuples, deciding `false` off
the atomic fragment. -/
theorem atomic_realize_computablePredIn (O : Set (ℕ →. ℕ))
    [IsComputableStructureIn O L] (k : ℕ) :
    ComputablePredIn O fun p : L.Formula (Fin k) × (Fin k → ℕ) ↦
      (p.1 : L.BoundedFormula (Fin k) 0).IsAtomic ∧ p.1.Realize p.2 := by
  obtain ⟨hdec, hcomp⟩ :=
    IsComputableStructureIn.relMap_computablePredIn (O := O) (L := L)
  have hwit : DecidablePred fun p : L.Formula (Fin k) × (Fin k → ℕ) ↦
      (p.1 : L.BoundedFormula (Fin k) 0).IsAtomic ∧ p.1.Realize p.2 := fun p ↦
    if hB : atomicSatBool p = true
    then Decidable.isTrue ((atomicSatBool_iff p).1 hB)
    else Decidable.isFalse fun h ↦ hB ((atomicSatBool_iff p).2 h)
  refine ⟨hwit, ?_⟩
  refine (computableIn_atomicSatAux O k hdec hcomp).of_eq fun p ↦ ?_
  have hdd : ∀ d : RelationApplicationData L ℕ,
      @decide _ (hdec d) = @decide _ (Classical.propDecidable d.relMap) := fun d ↦ by
    by_cases h : d.relMap <;> simp [h]
  have hBeq : (Option.casesOn (motive := fun _ ↦ Bool) (atomicData? p.1) false fun d ↦
      Sum.casesOn (motive := fun _ ↦ Bool) d
        (fun q ↦ decide (q.1.realize p.2 = q.2.realize p.2))
        fun q ↦
          Option.casesOn (motive := fun _ ↦ Bool)
            (RelationApplicationData.ofSymbolArgs?
              (q.1, q.2.map fun t ↦ t.realize p.2)) false
            fun d ↦ @decide _ (hdec d)) = atomicSatBool p := by
    rw [atomicSatBool]
    simp only [hdd]
  rw [hBeq]
  by_cases hB : atomicSatBool p = true
  · rw [hB]
    exact (@decide_eq_true _ (hwit p) ((atomicSatBool_iff p).1 hB)).symm
  · rw [Bool.not_eq_true] at hB
    rw [hB]
    refine (@decide_eq_false _ (hwit p) fun h ↦ ?_).symm
    rw [(atomicSatBool_iff p).2 h] at hB
    simp at hB

/-- The uniform subtype form: satisfaction of atomic formulas is a computable
predicate. -/
theorem atomicFormula_realize_computablePredIn (O : Set (ℕ →. ℕ))
    [IsComputableStructureIn O L] (k : ℕ) :
    ComputablePredIn O
      fun p : { φ : L.Formula (Fin k) //
          (φ : L.BoundedFormula (Fin k) 0).IsAtomic } × (Fin k → ℕ) ↦
      (p.1 : L.Formula (Fin k)).Realize p.2 :=
  ((atomic_realize_computablePredIn O k).comp
    ((Primrec.subtype_val.to_comp.computableIn.comp ComputableIn.fst).pair
      ComputableIn.snd)).of_eq fun p ↦ and_iff_right p.1.2

/-- The pointwise corollary: satisfaction of a fixed atomic formula is a computable
predicate on tuples. -/
theorem realize_computablePredIn_of_isAtomic (O : Set (ℕ →. ℕ))
    [IsComputableStructureIn O L] {k : ℕ} (φ : L.Formula (Fin k))
    (hφ : (φ : L.BoundedFormula (Fin k) 0).IsAtomic) :
    ComputablePredIn O fun v : Fin k → ℕ ↦ φ.Realize v :=
  (atomicFormula_realize_computablePredIn O k).comp
    ((ComputableIn.const (⟨φ, hφ⟩ : { φ : L.Formula (Fin k) //
      (φ : L.BoundedFormula (Fin k) 0).IsAtomic })).pair ComputableIn.id)

end AtomicSatisfaction

end FirstOrder.Language
