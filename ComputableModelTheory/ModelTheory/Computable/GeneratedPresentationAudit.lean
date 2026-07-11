/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.GeneratedPresentation
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for generated computable presentations

Named acceptance tests for the presentation packaging, checked by
`#assert_standard_axioms`. The two-presentation tests are the design gate: two
presentations on the carrier `ℕ` must be usable in a single statement without
structure-instance ambiguity. Outside the root import spine; CI checks it explicitly
with

```
lake env lean ComputableModelTheory/ModelTheory/Computable/GeneratedPresentationAudit.lean
```
-/

open Encodable FirstOrder Language Language.BoundedFormula

section

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-- The generator closure of a presentation is everything. -/
theorem test_closure_eq_top (P : GeneratedPresentationIn O L) :
    letI := P.toComputableStructure.inst
    Tuple.closure L P.gens = ⊤ :=
  P.closure_eq_top

/-- A presentation's complete atomic diagram is computable in the oracle. -/
theorem test_presentation_completeAtomicDiagram (P : GeneratedPresentationIn O L)
    (k : ℕ) : ComputablePredIn O (P.completeAtomicDiagram k) :=
  P.completeAtomicDiagram_computablePredIn k

/-- A presentation's complete quantifier-free diagram is computable in the oracle. -/
theorem test_presentation_completeQFDiagram (P : GeneratedPresentationIn O L)
    (k : ℕ) : ComputablePredIn O (P.completeQFDiagram k) :=
  P.completeQFDiagram_computablePredIn k

/-- The design gate: two presentations on the carrier `ℕ` coexist in one statement,
each with its own diagram computability, without instance ambiguity. -/
theorem test_two_presentations (P Q : GeneratedPresentationIn O L) (k : ℕ) :
    ComputablePredIn O (P.posAtomicDiagram k) ∧
      ComputablePredIn O (Q.negQFDiagram k) :=
  ⟨P.posAtomicDiagram_computablePredIn k, Q.negQFDiagram_computablePredIn k⟩

end

section ConcretePresentation

variable (O : Set (ℕ →. ℕ))

/-- The generators of the successor presentation. -/
theorem test_succPresentation_gens : (succPresentation O).gens = [0] :=
  rfl

/-- A second successor presentation with a redundant generator. -/
private def succPresentation2 : GeneratedPresentationIn O succLang :=
  letI := succStructure
  { toComputableStructure := ⟨succ_isComputable⟩
    gens := [0, 7]
    generates := eq_top_iff.2 (succ_tuple_generates ▸ Tuple.closure_mono (by simp)) }

/-- Two concrete presentations coexist with their diagram computabilities. -/
theorem test_concrete_two_presentations :
    ComputablePredIn O ((succPresentation O).posAtomicDiagram 2) ∧
      ComputablePredIn O ((succPresentation2 O).posAtomicDiagram 2) :=
  ⟨(succPresentation O).posAtomicDiagram_computablePredIn 2,
    (succPresentation2 O).posAtomicDiagram_computablePredIn 2⟩

end ConcretePresentation

#assert_standard_axioms test_closure_eq_top
#assert_standard_axioms test_presentation_completeAtomicDiagram
#assert_standard_axioms test_presentation_completeQFDiagram
#assert_standard_axioms test_two_presentations
#assert_standard_axioms test_succPresentation_gens
#assert_standard_axioms test_concrete_two_presentations
