/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.AtomicEquiv
import ComputableModelTheory.ModelTheory.Computable.GeneratedPresentation

/-!
# Effective failure of atomic equivalence

For two fixed generated computable presentations, the failure of atomic equivalence of
fixed-width tuples is r.e. in the oracle: a disagreement witness is an atomic formula
realized on one side and falsified on the other — a signed formula lying in one
presentation's complete atomic diagram but not the other's — and such witnesses are
found by searching over encoded atomic formulas. Each presentation's diagram
computability is obtained through its instance-free accessors, and the resulting
explicit predicates are combined outside any local structure-instance scope.
-/

open Encodable FirstOrder Language Language.BoundedFormula

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

namespace GeneratedPresentationIn

/-- Atomic equivalence of fixed-width tuples across two presentations' stored
structures. -/
def AtomicEquivTuples (P Q : GeneratedPresentationIn O L) {k : ℕ}
    (a b : Fin k → ℕ) : Prop :=
  @AtomicEquivalent L ℕ ℕ P.toComputableStructure.inst Q.toComputableStructure.inst
    k a b

/-- The failure of atomic equivalence between fixed tuples of two presentations is
r.e. in the oracle, by searching for a disagreeing signed atomic formula. -/
theorem not_atomicEquivTuples_rePredIn (P Q : GeneratedPresentationIn O L) {k : ℕ}
    (a b : Fin k → ℕ) :
    REPredIn O fun _ : Unit ↦ ¬P.AtomicEquivTuples Q a b := by
  have hPT : ComputablePredIn O fun φ : AtomicFormula L (Fin k) ↦
      P.completeAtomicDiagram k (true, φ, a) :=
    (P.completeAtomicDiagram_computablePredIn k).comp
      ((ComputableIn.const true).pair (ComputableIn.id.pair (ComputableIn.const a)))
  have hPF : ComputablePredIn O fun φ : AtomicFormula L (Fin k) ↦
      P.completeAtomicDiagram k (false, φ, a) :=
    (P.completeAtomicDiagram_computablePredIn k).comp
      ((ComputableIn.const false).pair (ComputableIn.id.pair (ComputableIn.const a)))
  have hQT : ComputablePredIn O fun φ : AtomicFormula L (Fin k) ↦
      Q.completeAtomicDiagram k (true, φ, b) :=
    (Q.completeAtomicDiagram_computablePredIn k).comp
      ((ComputableIn.const true).pair (ComputableIn.id.pair (ComputableIn.const b)))
  have hQF : ComputablePredIn O fun φ : AtomicFormula L (Fin k) ↦
      Q.completeAtomicDiagram k (false, φ, b) :=
    (Q.completeAtomicDiagram_computablePredIn k).comp
      ((ComputableIn.const false).pair (ComputableIn.id.pair (ComputableIn.const b)))
  obtain ⟨hDdec, hDcomp⟩ := (hPT.and hQF).or (hPF.and hQT)
  have hcase : ComputablePredIn O fun n : ℕ ↦
      (Option.casesOn (motive := fun _ ↦ Bool)
        (@decode (AtomicFormula L (Fin k)) Primcodable.toEncodable n) false
        fun φ ↦ @decide _ (hDdec φ)) = true := by
    refine ⟨fun n ↦ instDecidableEqBool _ true, ?_⟩
    have hB : ComputableIn O fun n : ℕ ↦
        Option.casesOn (motive := fun _ ↦ Bool)
          (@decode (AtomicFormula L (Fin k)) Primcodable.toEncodable n) false
          fun φ ↦ @decide _ (hDdec φ) :=
      ComputableIn.option_casesOn (Computable.decode.computableIn)
        (ComputableIn.const false) ((hDcomp.comp ComputableIn.snd).to₂)
    exact hB.of_eq fun n ↦ (Bool.decide_coe _).symm
  refine (REPredIn.exists_nat_of_computablePredIn
    (p := fun (_ : Unit) (n : ℕ) ↦
      (Option.casesOn (motive := fun _ ↦ Bool)
        (@decode (AtomicFormula L (Fin k)) Primcodable.toEncodable n) false
        fun φ ↦ @decide _ (hDdec φ)) = true)
    (hcase.comp ComputableIn.snd)).of_eq fun _ ↦ ?_
  constructor
  · rintro ⟨n, hn⟩
    rcases hd : @decode (AtomicFormula L (Fin k)) Primcodable.toEncodable n with - | φ
    · rw [hd] at hn
      exact absurd hn Bool.false_ne_true
    · rw [hd] at hn
      have hn' := of_decide_eq_true hn
      intro hAE
      have hiff := (@atomicEquivalent_iff_forall_atomicFormula L ℕ ℕ
        P.toComputableStructure.inst Q.toComputableStructure.inst k a b).1 hAE φ
      rcases hn' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ((Q.completeAtomicDiagram_false_iff φ b).1 h2)
          (hiff.1 ((P.completeAtomicDiagram_true_iff φ a).1 h1))
      · exact ((P.completeAtomicDiagram_false_iff φ a).1 h1)
          (hiff.2 ((Q.completeAtomicDiagram_true_iff φ b).1 h2))
  · intro hne
    have h1 : ¬∀ φ : AtomicFormula L (Fin k),
        (P.realize (φ : L.Formula (Fin k)) a ↔ Q.realize (φ : L.Formula (Fin k)) b) :=
      fun hall ↦ hne ((@atomicEquivalent_iff_forall_atomicFormula L ℕ ℕ
        P.toComputableStructure.inst Q.toComputableStructure.inst k a b).2 hall)
    obtain ⟨φ, hφ⟩ := not_forall.1 h1
    refine ⟨@encode (AtomicFormula L (Fin k)) Primcodable.toEncodable φ, ?_⟩
    rw [show @decode (AtomicFormula L (Fin k)) Primcodable.toEncodable
      (@encode (AtomicFormula L (Fin k)) Primcodable.toEncodable φ) = some φ from
      @encodek (AtomicFormula L (Fin k)) Primcodable.toEncodable φ]
    refine @decide_eq_true _ (hDdec φ) ?_
    by_cases hp : P.realize (φ : L.Formula (Fin k)) a
    · exact Or.inl ⟨(P.completeAtomicDiagram_true_iff φ a).2 hp,
        (Q.completeAtomicDiagram_false_iff φ b).2 fun hq ↦
          hφ ⟨fun _ ↦ hq, fun _ ↦ hp⟩⟩
    · refine Or.inr ⟨(P.completeAtomicDiagram_false_iff φ a).2 hp, ?_⟩
      refine (Q.completeAtomicDiagram_true_iff φ b).2 (by
        by_contra hq
        exact hφ ⟨fun hp' ↦ absurd hp' hp, fun hq' ↦ absurd hq' hq⟩)

/-- The generator form: for presentations with generator tuples of equal length, the
failure of atomic equivalence of the generators is r.e. in the oracle. -/
theorem not_atomicEquivGens_rePredIn (P Q : GeneratedPresentationIn O L)
    (h : P.gens.length = Q.gens.length) :
    REPredIn O fun _ : Unit ↦
      ¬P.AtomicEquivTuples Q P.generatorView fun i ↦ Q.generatorView (Fin.cast h i) :=
  P.not_atomicEquivTuples_rePredIn Q _ _

end GeneratedPresentationIn

end FirstOrder.Language
