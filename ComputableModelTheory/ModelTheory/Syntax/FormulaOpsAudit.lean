/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Syntax.FormulaOps
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for computable formula constructors

Named acceptance tests for the sigma-level formula constructors, checked by
`#assert_standard_axioms`. Outside the root import spine; CI checks it explicitly with

```
lake env lean ComputableModelTheory/ModelTheory/Syntax/FormulaOpsAudit.lean
```
-/

open Encodable FirstOrder Language Language.BoundedFormula

section

variable {L : Language} {α : Type*} [Primcodable α] [L.EffectiveLanguage]

omit [Primcodable α] [L.EffectiveLanguage] in
/-- Semantic gate: `sigmaEqual` applies `equal` on matching variable bounds. -/
theorem test_sigmaEqual_apply {n} (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    sigmaEqual ⟨n, t₁⟩ ⟨n, t₂⟩ = ⟨n, BoundedFormula.equal t₁ t₂⟩ :=
  sigmaEqual_apply

omit [Primcodable α] [L.EffectiveLanguage] in
/-- Semantic gate: `sigmaRel` applies `rel` on an arity-matched argument list of
constant variable bound. -/
theorem test_sigmaRel_apply {n k : ℕ} (R : L.Relations n)
    (ts : Fin n → L.Term (α ⊕ Fin k)) :
    sigmaRel ⟨n, R⟩ k ((List.finRange n).map fun i ↦ ⟨k, ts i⟩) =
      ⟨k, BoundedFormula.rel R ts⟩ :=
  sigmaRel_apply R ts

omit [Primcodable α] [L.EffectiveLanguage] in
/-- Semantic gate: `sigmaNot` is negation on the packaged formula. -/
theorem test_sigmaNot_apply {n} (φ : L.BoundedFormula α n) :
    sigmaNot ⟨n, φ⟩ = ⟨n, φ.not⟩ :=
  sigmaNot_apply φ

omit [Primcodable α] [L.EffectiveLanguage] in
/-- Semantic gate: `sigmaEx` is the existential on the packaged formula. -/
theorem test_sigmaEx_apply {n} (φ : L.BoundedFormula α (n + 1)) :
    sigmaEx ⟨n + 1, φ⟩ = ⟨n, φ.ex⟩ :=
  sigmaEx_apply φ

/-- The sigma-level falsum constructor is primitive recursive. -/
theorem test_primrec_sigmaFalsum :
    Primrec fun n : ℕ ↦ (⟨n, BoundedFormula.falsum⟩ : Σ n, L.BoundedFormula α n) :=
  primrec_sigmaFalsum

/-- The sigma-level equality constructor is primitive recursive. -/
theorem test_primrec_sigmaEqual : Primrec₂ (sigmaEqual (L := L) (α := α)) :=
  primrec₂_sigmaEqual

/-- The sigma-level relation constructor is primitive recursive. -/
theorem test_primrec_sigmaRel :
    Primrec fun q : (Σ m, L.Relations m) × ℕ × List (Σ k', L.Term (α ⊕ Fin k')) ↦
      sigmaRel q.1 q.2.1 q.2.2 :=
  primrec_sigmaRel

/-- Mathlib's sigma-level implication is primitive recursive. -/
theorem test_primrec_sigmaImp : Primrec₂ (sigmaImp (L := L) (α := α)) :=
  primrec₂_sigmaImp

/-- Mathlib's sigma-level universal quantifier is primitive recursive. -/
theorem test_primrec_sigmaAll : Primrec (sigmaAll (L := L) (α := α)) :=
  primrec_sigmaAll

/-- The sigma-level negation is primitive recursive. -/
theorem test_primrec_sigmaNot : Primrec (sigmaNot (L := L) (α := α)) :=
  primrec_sigmaNot

/-- The sigma-level existential quantifier is primitive recursive. -/
theorem test_primrec_sigmaEx : Primrec (sigmaEx (L := L) (α := α)) :=
  primrec_sigmaEx

/-- The public contract: all sigma-level constructors are computable. -/
theorem test_computable_sigmaImp : Computable₂ (sigmaImp (L := L) (α := α)) :=
  computable₂_sigmaImp

end

#assert_standard_axioms test_sigmaEqual_apply
#assert_standard_axioms test_sigmaRel_apply
#assert_standard_axioms test_sigmaNot_apply
#assert_standard_axioms test_sigmaEx_apply
#assert_standard_axioms test_primrec_sigmaFalsum
#assert_standard_axioms test_primrec_sigmaEqual
#assert_standard_axioms test_primrec_sigmaRel
#assert_standard_axioms test_primrec_sigmaImp
#assert_standard_axioms test_primrec_sigmaAll
#assert_standard_axioms test_primrec_sigmaNot
#assert_standard_axioms test_primrec_sigmaEx
#assert_standard_axioms test_computable_sigmaImp
