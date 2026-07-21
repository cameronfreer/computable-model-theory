/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.CePresentation

/-!
# Decidable-domain presentations

The generic decidable-domain presentation: a structure on a **computably decidable**
subset of ℕ — not an initial segment and not all of ℕ. This is the natural target of
certified constructions whose carriers are cut out by a decision procedure, such as
the canonical-representative domain of a c.e. structure chain under a decidable-stages
certificate: canonical codes form a decidable set with no reason to be an initial
segment. Conversion to an initial-segment presentation is a separate, later step
(through the enumeration-rank machinery), never an obligation of this type.

Following the total-code-data discipline, the structure data and the evaluators are
total on codes with on-domain correctness laws; because the domain is decidable, the
evaluators can be **total computable** functions, unlike the on-domain partial
evaluators of the c.e. level. A nonemptiness witness keeps the presented structure a
structure.

`toCePresentation` includes the decidable level into the c.e. level — the enumeration
sends non-members to the witness — with `toCePresentation_domain` as its preservation
theorem.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-- A presentation of a structure on a computably decidable subset of ℕ. Data is
total on codes; the domain laws are hypotheses. -/
structure DecidablePresentationIn (O : Set (ℕ →. ℕ)) (L : Language)
    [L.EffectiveLanguage] where
  /-- The structure data, total on codes; only its on-domain behavior is
  meaningful. -/
  str : L.Structure ℕ
  /-- The domain decision procedure. -/
  domainB : ℕ → Bool
  /-- The domain decision procedure is computable in the oracle. -/
  domainB_computableIn : ComputableIn O domainB
  /-- A domain element: presentations present nonempty structures. -/
  witness : ℕ
  witness_mem : domainB witness = true
  /-- The domain is closed under the interpretations of function symbols. -/
  domain_closed : ∀ (n : ℕ) (f : L.Functions n) (v : Fin n → ℕ),
    (∀ k, domainB (v k) = true) →
      domainB (@Structure.funMap L ℕ str n f v) = true
  /-- The total function evaluator. -/
  funEvalTotal : FunctionApplicationData L ℕ → ℕ
  /-- The function evaluator is computable in the oracle. -/
  funEvalTotal_computableIn : ComputableIn O funEvalTotal
  /-- On domain-valued arguments, the evaluator computes the interpretation. -/
  funEvalTotal_correct : ∀ d : FunctionApplicationData L ℕ,
    (∀ k, domainB (d.args k) = true) →
      funEvalTotal d = @FunctionApplicationData.funMap L ℕ str d
  /-- The total relation decider. -/
  relEvalTotal : RelationApplicationData L ℕ → Bool
  /-- The relation decider is computable in the oracle. -/
  relEvalTotal_computableIn : ComputableIn O relEvalTotal
  /-- On domain-valued arguments, the decider's verdict is the truth value. -/
  relEvalTotal_correct : ∀ d : RelationApplicationData L ℕ,
    (∀ k, domainB (d.args k) = true) →
      (relEvalTotal d = true ↔ @RelationApplicationData.relMap L ℕ str d)

namespace DecidablePresentationIn

variable (P : DecidablePresentationIn O L)

/-- The domain of a decidable presentation. -/
def domain : Set ℕ :=
  {x | P.domainB x = true}

theorem mem_domain_iff {x : ℕ} : x ∈ P.domain ↔ P.domainB x = true :=
  Iff.rfl

theorem witness_mem_domain : P.witness ∈ P.domain :=
  P.witness_mem

theorem domain_nonempty : P.domain.Nonempty :=
  ⟨P.witness, P.witness_mem⟩

/-- The domain membership predicate is computably decidable — the defining feature of
this level. -/
theorem domain_computablePredIn : ComputablePredIn O fun x ↦ x ∈ P.domain := by
  have inst : DecidablePred fun x ↦ x ∈ P.domain := fun x ↦
    decidable_of_iff (P.domainB x = true) Iff.rfl
  exact ⟨inst, P.domainB_computableIn.of_eq fun x ↦
    Bool.eq_iff_iff.2 (@decide_eq_true_iff _ (inst x)).symm⟩

/-! ### Inclusion into the c.e. level -/

/-- The enumeration underlying the c.e. inclusion: members enumerate themselves,
non-members fall back to the witness. -/
def ceEnum (n : ℕ) : ℕ :=
  bif P.domainB n then n else P.witness

theorem ceEnum_computableIn : ComputableIn O P.ceEnum :=
  ComputableIn.cond P.domainB_computableIn ComputableIn.id
    (ComputableIn.const P.witness)

/-- The range of the fallback enumeration is exactly the decidable domain. -/
theorem range_ceEnum : Set.range P.ceEnum = P.domain := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    unfold ceEnum
    by_cases h : P.domainB n = true
    · rw [h]
      exact h
    · rw [Bool.not_eq_true] at h
      rw [h]
      exact P.witness_mem
  · intro hx
    exact ⟨x, by rw [ceEnum, hx]; rfl⟩

/-- The inclusion of the decidable level into the c.e. level: the same structure
data, the fallback enumeration, and the total evaluators viewed as everywhere-halting
partial evaluators. -/
def toCePresentation : CePresentationIn O L where
  str := P.str
  enum := P.ceEnum
  enum_computableIn := P.ceEnum_computableIn
  domain_closed := fun n f v hv ↦ by
    rw [show Set.range P.ceEnum = P.domain from P.range_ceEnum] at hv ⊢
    exact P.domain_closed n f v hv
  funEval d := Part.some (P.funEvalTotal d)
  funEval_recursiveIn := P.funEvalTotal_computableIn
  funEval_correct := fun d hd ↦ by
    rw [P.funEvalTotal_correct d fun k ↦ by
      have := hd k
      rwa [show Set.range P.ceEnum = P.domain from P.range_ceEnum] at this]
    exact Part.mem_some _
  relEval d := Part.some (P.relEvalTotal d)
  relEval_recursiveIn := P.relEvalTotal_computableIn
  relEval_correct := fun d hd ↦
    ⟨P.relEvalTotal d, Part.mem_some _, P.relEvalTotal_correct d fun k ↦ by
      have := hd k
      rwa [show Set.range P.ceEnum = P.domain from P.range_ceEnum] at this⟩

/-- Preservation: the c.e. inclusion has the same domain. -/
@[simp]
theorem toCePresentation_domain : P.toCePresentation.domain = P.domain :=
  P.range_ceEnum

end DecidablePresentationIn

end FirstOrder.Language
