/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.CeStructureLimitEval
import ComputableModelTheory.ModelTheory.Computable.ComputableIso

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

/-! ### The stage maps at code level

The map before any bundling. Naming it, with its four facts, keeps the structural laws below free of
`Part.get`. -/

/-- The canonical code of a stage element. -/
noncomputable def stageCode {i x : ℕ} (hx : x ∈ (D.stageAt i).domain) : ℕ :=
  (D.toDomainChain.stageIntoPart i x).get (D.toDomainChain.stageIntoPart_dom hx)

theorem mem_stageIntoPart_stageCode {i x : ℕ} (hx : x ∈ (D.stageAt i).domain) :
    D.stageCode hx ∈ D.toDomainChain.stageIntoPart i x :=
  Part.get_mem _

theorem accepted_stageCode {i x : ℕ} (hx : x ∈ (D.stageAt i).domain) :
    D.toDomainChain.Accepted (D.stageCode hx) :=
  D.toDomainChain.accepted_of_mem_stageIntoPart hx (D.mem_stageIntoPart_stageCode hx)

/-- The code names the element's own class. -/
theorem limEquiv_stageCode {i x : ℕ} (hx : x ∈ (D.stageAt i).domain) :
    D.toDomainChain.limEquiv (i, x) (D.toDomainChain.rawRep (D.stageCode hx)) :=
  D.toDomainChain.limEquiv_of_mem_stageIntoPart hx (D.mem_stageIntoPart_stageCode hx)

theorem limMem_stageCode {i x : ℕ} (hx : x ∈ (D.stageAt i).domain) :
    D.toDomainChain.limMem (i, x) :=
  hx

/-- **Injective on its stage.** -/
theorem stageCode_injOn {i x y : ℕ} (hx : x ∈ (D.stageAt i).domain)
    (hy : y ∈ (D.stageAt i).domain) (h : D.stageCode hx = D.stageCode hy) : x = y :=
  D.toDomainChain.stageIntoPart_injOn hx hy (D.mem_stageIntoPart_stageCode hx)
    (h ▸ D.mem_stageIntoPart_stageCode hy)

/-! ### The structural laws

Stated at code level and proved through the semantic boundary only: no `Part.get`, no evaluator
internals, no common-stage bookkeeping. -/

/-- **Relations transfer both ways.** -/
theorem stageCode_relMap_iff {i n : ℕ} (R : L.Relations n) (v : Fin n → ℕ)
    (hv : ∀ k, v k ∈ (D.stageAt i).domain) :
    @Structure.RelMap L ℕ D.limitStr n R (fun k ↦ D.stageCode (hv k)) ↔
      @Structure.RelMap L ℕ (D.stageAt i).str n R v := by
  rw [D.limitStr_relMap_iff_limRelHolds R fun k ↦ D.stageCode (hv k)]
  rw [D.limRelHolds_iff_of_limEquiv R
      (v := fun k ↦ D.toDomainChain.rawRep (D.stageCode (hv k)))
      (v' := fun k ↦ (i, v k))
      (fun k ↦ D.toDomainChain.rawRep_limMem _) (fun k ↦ hv k)
      (fun k ↦ D.toDomainChain.limEquiv_symm (D.limEquiv_stageCode (hv k)))]
  exact D.limRelHolds_stage_iff R v hv

/-- **Functions transfer.** Both candidate outputs are accepted and satisfy the same limit graph, so
functionality gives `limEquiv` and accepted codes being equivalent only when equal closes it. -/
theorem stageCode_funMap {i n : ℕ} (f : L.Functions n) (v : Fin n → ℕ)
    (hv : ∀ k, v k ∈ (D.stageAt i).domain) :
    D.stageCode ((D.stageAt i).domain_closed n f v hv) =
      @Structure.funMap L ℕ D.limitStr n f (fun k ↦ D.stageCode (hv k)) := by
  set c₁ := D.stageCode ((D.stageAt i).domain_closed n f v hv) with hc₁
  set c₂ := @Structure.funMap L ℕ D.limitStr n f (fun k ↦ D.stageCode (hv k)) with hc₂
  have hacc₁ : D.toDomainChain.Accepted c₁ := D.accepted_stageCode _
  have hacc₂ : D.toDomainChain.Accepted c₂ := D.accepted_limitStr_funMap f _
  have hg₂ : D.LimFunGraph f (fun k ↦ D.toDomainChain.rawRep (D.stageCode (hv k)))
      (D.toDomainChain.rawRep c₂) := D.limitStr_funMap_limFunGraph f _
  have hg₁ : D.LimFunGraph f (fun k ↦ D.toDomainChain.rawRep (D.stageCode (hv k)))
      (D.toDomainChain.rawRep c₁) := by
    refine D.limFunGraph_of_limEquiv f (v := fun k ↦ (i, v k))
      (v' := fun k ↦ D.toDomainChain.rawRep (D.stageCode (hv k)))
      (out := (i, @Structure.funMap L ℕ (D.stageAt i).str n f v))
      (out' := D.toDomainChain.rawRep c₁)
      (fun k ↦ hv k) (fun k ↦ D.toDomainChain.rawRep_limMem _)
      (fun k ↦ D.limEquiv_stageCode (hv k))
      ((D.stageAt i).domain_closed n f v hv) (D.toDomainChain.rawRep_limMem _)
      (D.limEquiv_stageCode _) (D.limFunGraph_stage f v)
  exact (D.toDomainChain.accepted_limEquiv_iff hacc₁ hacc₂).1
    (D.limFunGraph_functional f (fun k ↦ D.toDomainChain.rawRep_limMem _) hg₁ hg₂
      (D.toDomainChain.rawRep_limMem _) (D.toDomainChain.rawRep_limMem _))

/-! ### The bundled stage embeddings

The induced subtype structures come from `ComputableIso`; that semantic bridge is imported for this
section alone. Bundling is thin — the three laws are already proved at code level — but
`stageEmbedding_apply_mem` matters: it is what connects the noncomputable bundled map back to the
uniformly partial recursive `stageIntoPart`. Without it the package would have a semantic embedding
and a computable map with no stated relation between them. -/

/-- **The stage embedding.** -/
noncomputable def stageEmbedding (U : D.UniformEvaluatorsIn) (i : ℕ) :
    (D.stageAt i).domain ↪[L] (D.limitPresentation U).domain where
  toFun x := ⟨D.stageCode x.2, by
    rw [D.limitPresentation_domain]
    exact D.accepted_stageCode x.2⟩
  inj' x y h :=
    Subtype.ext (D.stageCode_injOn x.2 y.2 (congrArg Subtype.val h))
  map_fun' {n} f v := Subtype.ext (D.stageCode_funMap f (fun k ↦ (v k).1) fun k ↦ (v k).2)
  map_rel' {n} R v := D.stageCode_relMap_iff R (fun k ↦ (v k).1) fun k ↦ (v k).2

@[simp] theorem stageEmbedding_coe (U : D.UniformEvaluatorsIn) (i : ℕ)
    (x : (D.stageAt i).domain) :
    ((D.stageEmbedding U i x : (D.limitPresentation U).domain) : ℕ) = D.stageCode x.2 :=
  rfl

/-- **The computational bridge.** The bundled embedding's value is a value of the uniformly partial
recursive stage map — the only statement tying the semantic side of the package to its effective
side. -/
theorem stageEmbedding_apply_mem (U : D.UniformEvaluatorsIn) (i : ℕ)
    (x : (D.stageAt i).domain) :
    ((D.stageEmbedding U i x : (D.limitPresentation U).domain) : ℕ) ∈
      D.toDomainChain.stageIntoPart i x.1 :=
  D.mem_stageIntoPart_stageCode x.2

/-! ### Coherence and coverage

Coherence is inherited from the *search*, not re-derived: `stageIntoPart_step` is an equation
between `Part`s, so the code-level and bundled forms are both `Part.mem_unique`. -/

/-- **Codes agree along a step.** -/
theorem stageCode_step {i : ℕ} {x : ℕ} (hx : x ∈ (D.stageAt i).domain) :
    ∃ y ∈ D.toDomainChain.step i x, ∃ hy : y ∈ (D.stageAt (i + 1)).domain,
      D.stageCode hx = D.stageCode hy := by
  obtain ⟨y, hy, hydom, heq⟩ := D.toDomainChain.stageIntoPart_step hx
  exact ⟨y, hy, hydom, Part.mem_unique (D.mem_stageIntoPart_stageCode hx)
    (heq ▸ D.mem_stageIntoPart_stageCode hydom)⟩

/-- The bundled form. -/
theorem stageEmbedding_step (U : D.UniformEvaluatorsIn) {i x : ℕ}
    (hx : x ∈ (D.stageAt i).domain) :
    ∃ y ∈ D.toDomainChain.step i x, ∃ hy : y ∈ (D.stageAt (i + 1)).domain,
      D.stageEmbedding U i ⟨x, hx⟩ = D.stageEmbedding U (i + 1) ⟨y, hy⟩ := by
  obtain ⟨y, hy, hydom, heq⟩ := D.stageCode_step hx
  exact ⟨y, hy, hydom, Subtype.ext heq⟩

/-- **Coverage.** Every carrier element is a stage image — with the stage and the element named, so
the limit is the union of the stage embeddings' ranges. -/
theorem exists_stageEmbedding_eq (U : D.UniformEvaluatorsIn)
    (c : (D.limitPresentation U).domain) :
    ∃ (i : ℕ) (x : ℕ) (hx : x ∈ (D.stageAt i).domain),
      D.stageEmbedding U i ⟨x, hx⟩ = c := by
  have hacc : D.toDomainChain.Accepted (c : ℕ) :=
    (Set.ext_iff.1 (D.limitPresentation_domain U) (c : ℕ)).1 c.2
  have hmem : (D.toDomainChain.rawRep (c : ℕ)).2 ∈
      (D.stageAt (D.toDomainChain.rawRep (c : ℕ)).1).domain :=
    D.toDomainChain.rawRep_limMem _
  refine ⟨_, _, hmem, Subtype.ext ?_⟩
  exact Part.mem_unique (D.mem_stageIntoPart_stageCode hmem)
    (D.toDomainChain.mem_stageIntoPart_rawRep_of_accepted hacc)

end CeStructureChainIn

end FirstOrder.Language
