/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.Diagram
import ComputableModelTheory.ModelTheory.Computable.SuccExample
import Mathlib.ModelTheory.Bundled

/-!
# Generated computable presentations

A generated presentation bundles an ω-presented computable structure on `ℕ` with a
finite list tuple of generators whose closure is the whole structure. The stored
structure is deliberately **not** installed as a global instance: two presentations on
the carrier `ℕ` must coexist in one statement without instance ambiguity, so every
accessor and theorem installs the stored structure locally with `letI` and exposes an
instance-free interface (`realize`, the signed diagram predicates, and their
computability).
-/

open Encodable FirstOrder Language Language.BoundedFormula

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-- A generated computable presentation: a bundled computable structure on `ℕ`
together with a generating list tuple. -/
structure GeneratedPresentationIn (O : Set (ℕ →. ℕ)) (L : Language)
    [L.EffectiveLanguage] where
  /-- The bundled ω-presented computable structure. -/
  toComputableStructure : ComputableStructureIn O L
  /-- The generator tuple. -/
  gens : Tuple ℕ
  /-- The generators generate the stored structure. -/
  generates : @Tuple.Generates ℕ L toComputableStructure.inst gens

namespace GeneratedPresentationIn

variable (P : GeneratedPresentationIn O L)

/-- The presentation as a bundled structure. -/
def toBundled : CategoryTheory.Bundled L.Structure :=
  ⟨ℕ, P.toComputableStructure.inst⟩

/-- The structure on the bundled carrier, keyed on `toBundled` so that it is found
without an ambient structure on the raw carrier. -/
instance instStructureToBundled (P : GeneratedPresentationIn O L) :
    L.Structure ↥P.toBundled :=
  P.toComputableStructure.inst

/-- The fixed-width view of the generator tuple. -/
def generatorView : Fin P.gens.length → ℕ :=
  P.gens.view

/-- Realization of a formula in the stored structure. -/
def realize {k : ℕ} (φ : L.Formula (Fin k)) (v : Fin k → ℕ) : Prop :=
  letI := P.toComputableStructure.inst
  φ.Realize v

/-- The generator tuple's closure in the stored structure is everything. -/
theorem closure_eq_top :
    letI := P.toComputableStructure.inst
    Tuple.closure L P.gens = ⊤ :=
  P.generates

/-- The positive atomic diagram of the stored structure at width `k`. -/
def posAtomicDiagram (k : ℕ) : L.Formula (Fin k) × (Fin k → ℕ) → Prop :=
  letI := P.toComputableStructure.inst
  FirstOrder.Language.posAtomicDiagram L k

/-- The negative atomic diagram of the stored structure at width `k`. -/
def negAtomicDiagram (k : ℕ) : L.Formula (Fin k) × (Fin k → ℕ) → Prop :=
  letI := P.toComputableStructure.inst
  FirstOrder.Language.negAtomicDiagram L k

/-- The complete atomic diagram of the stored structure at width `k`. -/
def completeAtomicDiagram (k : ℕ) :
    Bool × AtomicFormula L (Fin k) × (Fin k → ℕ) → Prop :=
  letI := P.toComputableStructure.inst
  FirstOrder.Language.completeAtomicDiagram L k

/-- The positive quantifier-free diagram of the stored structure at width `k`. -/
def posQFDiagram (k : ℕ) : L.Formula (Fin k) × (Fin k → ℕ) → Prop :=
  letI := P.toComputableStructure.inst
  FirstOrder.Language.posQFDiagram L k

/-- The negative quantifier-free diagram of the stored structure at width `k`. -/
def negQFDiagram (k : ℕ) : L.Formula (Fin k) × (Fin k → ℕ) → Prop :=
  letI := P.toComputableStructure.inst
  FirstOrder.Language.negQFDiagram L k

/-- The complete quantifier-free diagram of the stored structure at width `k`. -/
def completeQFDiagram (k : ℕ) : Bool × QFFormula L (Fin k) × (Fin k → ℕ) → Prop :=
  letI := P.toComputableStructure.inst
  FirstOrder.Language.completeQFDiagram L k

/-- The positive sign of a presentation's complete atomic diagram is realization in
the stored structure. -/
theorem completeAtomicDiagram_true_iff {k : ℕ} (φ : AtomicFormula L (Fin k))
    (v : Fin k → ℕ) :
    P.completeAtomicDiagram k (true, φ, v) ↔ P.realize (φ : L.Formula (Fin k)) v := by
  letI := P.toComputableStructure.inst
  exact FirstOrder.Language.completeAtomicDiagram_true L k φ v

/-- The negative sign of a presentation's complete atomic diagram is falsification in
the stored structure. -/
theorem completeAtomicDiagram_false_iff {k : ℕ} (φ : AtomicFormula L (Fin k))
    (v : Fin k → ℕ) :
    P.completeAtomicDiagram k (false, φ, v) ↔
      ¬P.realize (φ : L.Formula (Fin k)) v := by
  letI := P.toComputableStructure.inst
  exact FirstOrder.Language.completeAtomicDiagram_false L k φ v

/-- The presentation's positive atomic diagram is computable in the oracle. -/
theorem posAtomicDiagram_computablePredIn (k : ℕ) :
    ComputablePredIn O (P.posAtomicDiagram k) := by
  letI := P.toComputableStructure.inst
  haveI := P.toComputableStructure.isComputable
  exact FirstOrder.Language.posAtomicDiagram_computablePredIn O

/-- The presentation's negative atomic diagram is computable in the oracle. -/
theorem negAtomicDiagram_computablePredIn (k : ℕ) :
    ComputablePredIn O (P.negAtomicDiagram k) := by
  letI := P.toComputableStructure.inst
  haveI := P.toComputableStructure.isComputable
  exact FirstOrder.Language.negAtomicDiagram_computablePredIn O

/-- The presentation's complete atomic diagram is computable in the oracle. -/
theorem completeAtomicDiagram_computablePredIn (k : ℕ) :
    ComputablePredIn O (P.completeAtomicDiagram k) := by
  letI := P.toComputableStructure.inst
  haveI := P.toComputableStructure.isComputable
  exact FirstOrder.Language.completeAtomicDiagram_computablePredIn O

/-- The presentation's positive quantifier-free diagram is computable in the
oracle. -/
theorem posQFDiagram_computablePredIn (k : ℕ) :
    ComputablePredIn O (P.posQFDiagram k) := by
  letI := P.toComputableStructure.inst
  haveI := P.toComputableStructure.isComputable
  exact FirstOrder.Language.posQFDiagram_computablePredIn O

/-- The presentation's negative quantifier-free diagram is computable in the
oracle. -/
theorem negQFDiagram_computablePredIn (k : ℕ) :
    ComputablePredIn O (P.negQFDiagram k) := by
  letI := P.toComputableStructure.inst
  haveI := P.toComputableStructure.isComputable
  exact FirstOrder.Language.negQFDiagram_computablePredIn O

/-- The presentation's complete quantifier-free diagram is computable in the
oracle. -/
theorem completeQFDiagram_computablePredIn (k : ℕ) :
    ComputablePredIn O (P.completeQFDiagram k) := by
  letI := P.toComputableStructure.inst
  haveI := P.toComputableStructure.isComputable
  exact FirstOrder.Language.completeQFDiagram_computablePredIn O

end GeneratedPresentationIn

/-- The successor presentation on `ℕ`, generated by the tuple `[0]`. -/
def succPresentation (O : Set (ℕ →. ℕ)) : GeneratedPresentationIn O succLang :=
  letI := succStructure
  { toComputableStructure := ⟨succ_isComputable⟩
    gens := [0]
    generates := succ_tuple_generates }

end FirstOrder.Language
