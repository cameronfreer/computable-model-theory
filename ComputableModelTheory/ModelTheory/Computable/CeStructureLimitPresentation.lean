/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.CeStructureLimitEval

/-!
# The Level-1 extensional limit presentation

The uncertified direct limit as a `CePresentationIn`, with the accepted codes as its carrier.

**Unconditional evaluation is what makes this clean.** The `RankPresentation` layer has to default
its structure off-domain, because its evaluator only halts where the rank data says it should. Here
neither pipeline needs a guard: every coded application halts, so the structure is defined by
`Part.get` outright and the carrier hypotheses in all three presentation laws go unused
computationally. `accepted_limitStr_funMap` records the sharp form — *every* function application
returns an accepted code, even on arguments that name nothing — which is why no defensive guard
belongs in the structure either.

The structure is an opaque `def` with named equation lemmas, deliberately not an `abbrev`. A
reducible definition sitting above a partial pipeline unfolds during computability proofs and sends
`whnf` chasing the whole thing; that is the same trap `argStage` fell into.

`limitStr_funMap_limFunGraph` and `limitStr_relMap_iff_limRelHolds` are the interface everything
above this file should use. Below that boundary live `Part.get`, the evaluator internals, and the
common-stage bookkeeping; above it, only the limit semantics of `CeStructureChain`.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

namespace CeStructureChainIn

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable (D : CeStructureChainIn O L)

/-! ### The total structure

Total because evaluation is unconditional — no defaulting, no guard. -/

/-- The limit structure on codes. `implicit_reducible` rather than `reducible`: instance search may
unfold it, ordinary elaboration may not. A plainly reducible structure sitting above a partial
pipeline is what sends the computability proofs' `whnf` chasing the evaluator. -/
@[implicit_reducible]
noncomputable def limitStr : L.Structure ℕ where
  funMap {_} f v :=
    (D.rawFunEvalPart (FunctionApplicationData.ofFixed f v)).get (D.rawFunEvalPart_dom _)
  RelMap {_} R v := true ∈ D.rawRelEvalPart (RelationApplicationData.ofFixed R v)

@[simp] theorem limitStr_funMap {n : ℕ} (f : L.Functions n) (v : Fin n → ℕ) :
    @Structure.funMap L ℕ D.limitStr n f v =
      (D.rawFunEvalPart (FunctionApplicationData.ofFixed f v)).get (D.rawFunEvalPart_dom _) :=
  rfl

@[simp] theorem limitStr_relMap {n : ℕ} (R : L.Relations n) (v : Fin n → ℕ) :
    @Structure.RelMap L ℕ D.limitStr n R v ↔
      true ∈ D.rawRelEvalPart (RelationApplicationData.ofFixed R v) :=
  Iff.rfl

/-- **Every function application returns an accepted code** — including applications to codes that
name nothing. Recorded separately because it is why no defensive guard belongs in the structure: the
carrier hypothesis of `domain_closed` is not doing any work. -/
theorem accepted_limitStr_funMap {n : ℕ} (f : L.Functions n) (v : Fin n → ℕ) :
    D.toDomainChain.Accepted (@Structure.funMap L ℕ D.limitStr n f v) :=
  accepted_of_mem_rawFunEvalPart (Part.get_mem _)

/-! ### The presentation -/

/-- **The Level-1 extensional limit**, as a c.e. presentation: the accepted codes with the limit
structure. No certificate, and no membership test in the enumeration — the accepted codes are
exactly the range of canonicalization. -/
noncomputable def limitPresentation (U : D.UniformEvaluatorsIn) : CePresentationIn O L where
  str := D.limitStr
  enum := D.toDomainChain.canonicalRaw
  enum_computableIn := D.toDomainChain.canonicalRaw_computableIn
  domain_closed := fun _ f v _ ↦ by
    rw [D.toDomainChain.range_canonicalRaw]
    exact D.accepted_limitStr_funMap f v
  funEval := D.rawFunEvalPart
  funEval_recursiveIn := D.rawFunEvalPart_recursiveIn U
  funEval_correct := fun _ _ ↦ Part.get_mem _
  relEval := D.rawRelEvalPart
  relEval_recursiveIn := D.rawRelEvalPart_recursiveIn U
  relEval_correct := fun d _ ↦ by
    obtain ⟨b, hb⟩ := Part.dom_iff_mem.1 (D.rawRelEvalPart_dom d)
    refine ⟨b, hb, ?_⟩
    constructor
    · rintro rfl
      exact hb
    · intro h
      exact Part.mem_unique hb h

@[simp] theorem limitPresentation_str (U : D.UniformEvaluatorsIn) :
    (D.limitPresentation U).str = D.limitStr :=
  rfl

@[simp] theorem limitPresentation_enum (U : D.UniformEvaluatorsIn) :
    (D.limitPresentation U).enum = D.toDomainChain.canonicalRaw :=
  rfl

/-- **The carrier is exactly the accepted codes.** -/
theorem limitPresentation_domain (U : D.UniformEvaluatorsIn) :
    (D.limitPresentation U).domain = {n | D.toDomainChain.Accepted n} :=
  D.toDomainChain.range_canonicalRaw

/-! ### The semantic interface

Everything above this file should use these two and nothing else: `Part.get`, the evaluator
internals and the common-stage bookkeeping all stay below the boundary. -/

/-- The structure's function values are the limit's, on the arguments' classes. -/
theorem limitStr_funMap_limFunGraph {n : ℕ} (f : L.Functions n) (v : Fin n → ℕ) :
    D.LimFunGraph f (fun k ↦ D.toDomainChain.rawRep (v k))
      (D.toDomainChain.rawRep (@Structure.funMap L ℕ D.limitStr n f v)) :=
  limFunGraph_of_mem_rawFunEvalPart (d := FunctionApplicationData.ofFixed f v) (Part.get_mem _)

/-- And the structure's relations are the limit's. -/
theorem limitStr_relMap_iff_limRelHolds {n : ℕ} (R : L.Relations n) (v : Fin n → ℕ) :
    @Structure.RelMap L ℕ D.limitStr n R v ↔
      D.LimRelHolds R fun k ↦ D.toDomainChain.rawRep (v k) := by
  obtain ⟨b, hb, hiff⟩ := D.rawRelEvalPart_spec (RelationApplicationData.ofFixed R v)
  rw [limitStr_relMap]
  constructor
  · intro h
    exact hiff.1 (Part.mem_unique hb h)
  · intro h
    exact (hiff.2 h) ▸ hb

end CeStructureChainIn

end FirstOrder.Language
