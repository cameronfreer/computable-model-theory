/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.QFSatisfaction

/-!
# Computable atomic and quantifier-free diagrams

The roadmap PR 8 first half: signed diagram predicates at a fixed variable width `k`,
with their computability in ω-presented computable structures. The positive diagram
holds on the atomic (respectively quantifier-free) formulas realized by a tuple, the
negative diagram on those falsified, and the complete diagram pairs a subtype-packaged
formula with a Boolean selecting positive or negative truth.

All predicates are stated at a fixed width over `L.Formula (Fin k) × (Fin k → ℕ)`
(complete forms over `Bool × AtomicFormula L (Fin k) × (Fin k → ℕ)` and its
quantifier-free analogue). A single uniform carrier packaging the width — a
`Primcodable` instance for `Σ k, L.Formula (Fin k) × (Fin k → ℕ)` — is a separate
future acceptance gate and is deliberately not assumed here. Diagrams of c.e.
structures are likewise deferred until the r.e. dovetailing substrate (finite
conjunction and existential closure over an oracle) lands.

These predicates are the single-structure components of the eventual nonembedding
witness: a candidate map between presentations fails to be a partial embedding exactly
when some atomic formula `φ` and tuples `a`, `b` satisfy
`φ.Realize a ≠ φ.Realize b` across the two structures — that is, when some
`(b, φ, ·)` lies in one complete atomic diagram but not the other. The two-structure
packaging is left to the embedding layer.
-/

open Encodable FirstOrder Language Language.BoundedFormula

namespace FirstOrder.Language

variable (L : Language) [L.Structure ℕ] (k : ℕ)

section Diagrams

/-- Membership in the positive atomic diagram at width `k`: an atomic formula together
with a realizing tuple. -/
def posAtomicDiagram (p : L.Formula (Fin k) × (Fin k → ℕ)) : Prop :=
  (p.1 : L.BoundedFormula (Fin k) 0).IsAtomic ∧ p.1.Realize p.2

/-- Membership in the negative atomic diagram at width `k`: an atomic formula together
with a falsifying tuple. -/
def negAtomicDiagram (p : L.Formula (Fin k) × (Fin k → ℕ)) : Prop :=
  (p.1 : L.BoundedFormula (Fin k) 0).IsAtomic ∧ ¬p.1.Realize p.2

/-- Membership in the complete atomic diagram at width `k`: a signed atomic formula
with the Boolean selecting positive or negative truth. -/
def completeAtomicDiagram (q : Bool × AtomicFormula L (Fin k) × (Fin k → ℕ)) : Prop :=
  q.1 = true ↔ (q.2.1 : L.Formula (Fin k)).Realize q.2.2

/-- Membership in the positive quantifier-free diagram at width `k`. -/
def posQFDiagram (p : L.Formula (Fin k) × (Fin k → ℕ)) : Prop :=
  (p.1 : L.BoundedFormula (Fin k) 0).IsQF ∧ p.1.Realize p.2

/-- Membership in the negative quantifier-free diagram at width `k`. -/
def negQFDiagram (p : L.Formula (Fin k) × (Fin k → ℕ)) : Prop :=
  (p.1 : L.BoundedFormula (Fin k) 0).IsQF ∧ ¬p.1.Realize p.2

/-- Membership in the complete quantifier-free diagram at width `k`. -/
def completeQFDiagram (q : Bool × QFFormula L (Fin k) × (Fin k → ℕ)) : Prop :=
  q.1 = true ↔ (q.2.1 : L.Formula (Fin k)).Realize q.2.2

/-- The positive sign of the complete atomic diagram is realization. -/
@[simp]
theorem completeAtomicDiagram_true (φ : AtomicFormula L (Fin k)) (v : Fin k → ℕ) :
    completeAtomicDiagram L k (true, φ, v) ↔ (φ : L.Formula (Fin k)).Realize v := by
  rw [completeAtomicDiagram]
  simp

/-- The negative sign of the complete atomic diagram is falsification. -/
@[simp]
theorem completeAtomicDiagram_false (φ : AtomicFormula L (Fin k)) (v : Fin k → ℕ) :
    completeAtomicDiagram L k (false, φ, v) ↔ ¬(φ : L.Formula (Fin k)).Realize v := by
  rw [completeAtomicDiagram]
  simp

/-- The positive sign of the complete quantifier-free diagram is realization. -/
@[simp]
theorem completeQFDiagram_true (φ : QFFormula L (Fin k)) (v : Fin k → ℕ) :
    completeQFDiagram L k (true, φ, v) ↔ (φ : L.Formula (Fin k)).Realize v := by
  rw [completeQFDiagram]
  simp

/-- The negative sign of the complete quantifier-free diagram is falsification. -/
@[simp]
theorem completeQFDiagram_false (φ : QFFormula L (Fin k)) (v : Fin k → ℕ) :
    completeQFDiagram L k (false, φ, v) ↔ ¬(φ : L.Formula (Fin k)).Realize v := by
  rw [completeQFDiagram]
  simp

end Diagrams

section Computability

variable {L k} [L.EffectiveLanguage] (O : Set (ℕ →. ℕ)) [IsComputableStructureIn O L]

/-- The positive atomic diagram of a computable structure is computable in the
oracle. -/
theorem posAtomicDiagram_computablePredIn :
    ComputablePredIn O (posAtomicDiagram L k) :=
  (atomic_realize_computablePredIn O k).of_eq fun _ ↦ Iff.rfl

/-- The negative atomic diagram of a computable structure is computable in the
oracle. -/
theorem negAtomicDiagram_computablePredIn :
    ComputablePredIn O (negAtomicDiagram L k) := by
  obtain ⟨hd, hp⟩ := primrecPred_formula_isAtomic (L := L) (α := Fin k)
  have hA : ComputablePredIn O fun p : L.Formula (Fin k) × (Fin k → ℕ) ↦
      (p.1 : L.BoundedFormula (Fin k) 0).IsAtomic :=
    ComputablePredIn.comp ⟨hd, hp.to_comp.computableIn⟩ ComputableIn.fst
  refine (hA.and (atomic_realize_computablePredIn O k).not).of_eq fun p ↦ ?_
  rw [negAtomicDiagram]
  tauto

/-- The complete atomic diagram of a computable structure is computable in the
oracle. -/
theorem completeAtomicDiagram_computablePredIn :
    ComputablePredIn O (completeAtomicDiagram L k) := by
  obtain ⟨hd, hp⟩ := (Primrec.eq.comp Primrec.fst (Primrec.const true) :
    PrimrecPred fun q : Bool × AtomicFormula L (Fin k) × (Fin k → ℕ) ↦ q.1 = true)
  have hb : ComputablePredIn O
      fun q : Bool × AtomicFormula L (Fin k) × (Fin k → ℕ) ↦ q.1 = true :=
    ⟨hd, hp.to_comp.computableIn⟩
  have hr : ComputablePredIn O
      fun q : Bool × AtomicFormula L (Fin k) × (Fin k → ℕ) ↦
      (q.2.1 : L.Formula (Fin k)).Realize q.2.2 :=
    (atomicFormula_realize_computablePredIn O k).comp ComputableIn.snd
  exact (hb.iff hr).of_eq fun q ↦ by rw [completeAtomicDiagram]

/-- The positive quantifier-free diagram of a computable structure is computable in
the oracle. -/
theorem posQFDiagram_computablePredIn : ComputablePredIn O (posQFDiagram L k) :=
  (qf_realize_computablePredIn O k).of_eq fun _ ↦ Iff.rfl

/-- The negative quantifier-free diagram of a computable structure is computable in
the oracle. -/
theorem negQFDiagram_computablePredIn : ComputablePredIn O (negQFDiagram L k) := by
  obtain ⟨hd, hp⟩ := primrecPred_formula_isQF (L := L) (α := Fin k)
  have hQ : ComputablePredIn O fun p : L.Formula (Fin k) × (Fin k → ℕ) ↦
      (p.1 : L.BoundedFormula (Fin k) 0).IsQF :=
    ComputablePredIn.comp ⟨hd, hp.to_comp.computableIn⟩ ComputableIn.fst
  refine (hQ.and (qf_realize_computablePredIn O k).not).of_eq fun p ↦ ?_
  rw [negQFDiagram]
  tauto

/-- The complete quantifier-free diagram of a computable structure is computable in
the oracle. -/
theorem completeQFDiagram_computablePredIn :
    ComputablePredIn O (completeQFDiagram L k) := by
  obtain ⟨hd, hp⟩ := (Primrec.eq.comp Primrec.fst (Primrec.const true) :
    PrimrecPred fun q : Bool × QFFormula L (Fin k) × (Fin k → ℕ) ↦ q.1 = true)
  have hb : ComputablePredIn O
      fun q : Bool × QFFormula L (Fin k) × (Fin k → ℕ) ↦ q.1 = true :=
    ⟨hd, hp.to_comp.computableIn⟩
  have hr : ComputablePredIn O fun q : Bool × QFFormula L (Fin k) × (Fin k → ℕ) ↦
      (q.2.1 : L.Formula (Fin k)).Realize q.2.2 :=
    (qfFormula_realize_computablePredIn O k).comp ComputableIn.snd
  exact (hb.iff hr).of_eq fun q ↦ by rw [completeQFDiagram]

end Computability

end FirstOrder.Language
