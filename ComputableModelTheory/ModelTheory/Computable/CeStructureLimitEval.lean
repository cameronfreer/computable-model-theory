/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.CeStructureChain
import ComputableModelTheory.Computability.CeDomainCanonical

/-!
# The evaluators of the uncertified Level-1 limit

The last computational component. Both pipelines share the common-stage transport of
`CeDomainCanonical` and diverge only afterwards:

```
function: transportRawArgsPart → ofSymbolArgs? → stage funEval → canonicalPart (M, y)
relation: transportRawArgsPart → ofSymbolArgs? → stage relEval
```

Two shapes are load-bearing.

**Halting is unconditional.** Every natural number's `rawRep` is valid, so the transport always
halts; the reassembly always succeeds because traversal preserves length; the stage evaluator always
halts because the transported arguments are all in that stage; and canonicalization always halts
because the stage's own value is again in that stage. No `Accepted` guard appears anywhere — codes
need not name limit elements for evaluation to be defined.

**The raw output pair is named.** `limMem_rawFunOutput` says `(M, y)` is a valid representative, and
that single fact supplies both the halting of the final canonicalization and the semantic theorem:
`limEquiv (M, y) (rawRep c)` turns the stage computation directly into `LimFunGraph`. Relations reuse
everything up to the stage evaluation and omit only that last step.

The definitions are written in exactly the `bind`/`map` association their `RecursiveIn` proofs
follow. That is a definition-time decision, not a proof detail: a monad-equivalent reassociation is
equal as `Part`s but a different term, and closing the computability proof would then send `whnf`
through the whole pipeline.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

namespace CeStructureChainIn

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable (D : CeStructureChainIn O L)

/-- The common stage of a coded argument tuple. -/
abbrev argStage (l : List ℕ) : ℕ :=
  D.toDomainChain.rawStageBound l

/-! ### The two pipelines -/

/-- Function evaluation on codes: transport the arguments to a common stage, reassemble application
data there, evaluate, and canonicalize the raw output. -/
noncomputable def rawFunEvalPart (d : FunctionApplicationData L ℕ) : Part ℕ :=
  (D.toDomainChain.transportRawArgsPart d.argsList).bind fun src ↦
    ((FunctionApplicationData.ofSymbolArgs? (d.toSymbol, src) :
        Option (FunctionApplicationData L ℕ)) : Part (FunctionApplicationData L ℕ)).bind fun d' ↦
      ((D.stageAt (D.argStage d.argsList)).funEval d').bind fun y ↦
        D.toDomainChain.canonicalPart (D.argStage d.argsList, y)

/-- Relation evaluation on codes: the same, stopping at the stage evaluator. -/
noncomputable def rawRelEvalPart (d : RelationApplicationData L ℕ) : Part Bool :=
  (D.toDomainChain.transportRawArgsPart d.argsList).bind fun src ↦
    ((RelationApplicationData.ofSymbolArgs? (d.toSymbol, src) :
        Option (RelationApplicationData L ℕ)) : Part (RelationApplicationData L ℕ)).bind fun d' ↦
      (D.stageAt (D.argStage d.argsList)).relEval d'

variable {D}

theorem mem_rawFunEvalPart_iff {d : FunctionApplicationData L ℕ} {c : ℕ} :
    c ∈ D.rawFunEvalPart d ↔
      ∃ src ∈ D.toDomainChain.transportRawArgsPart d.argsList,
        ∃ d' ∈ (FunctionApplicationData.ofSymbolArgs? (d.toSymbol, src) :
            Option (FunctionApplicationData L ℕ)),
          ∃ y ∈ (D.stageAt (D.argStage d.argsList)).funEval d',
            c ∈ D.toDomainChain.canonicalPart (D.argStage d.argsList, y) := by
  rw [rawFunEvalPart]
  simp only [Part.mem_bind_iff, Part.mem_ofOption]

theorem mem_rawRelEvalPart_iff {d : RelationApplicationData L ℕ} {b : Bool} :
    b ∈ D.rawRelEvalPart d ↔
      ∃ src ∈ D.toDomainChain.transportRawArgsPart d.argsList,
        ∃ d' ∈ (RelationApplicationData.ofSymbolArgs? (d.toSymbol, src) :
            Option (RelationApplicationData L ℕ)),
          b ∈ (D.stageAt (D.argStage d.argsList)).relEval d' := by
  rw [rawRelEvalPart]
  simp only [Part.mem_bind_iff, Part.mem_ofOption]

/-! ### The transported arguments

Shared by both pipelines: length preservation makes the reassembly succeed, and membership in the
common stage makes the stage evaluator halt. -/

theorem transported_length {l src : List ℕ}
    (h : src ∈ D.toDomainChain.transportRawArgsPart l) : src.length = l.length :=
  (List.Forall₂.length_eq (D.toDomainChain.mem_transportRawArgsPart_iff.1 h)).symm

theorem transported_mem_stage {l src : List ℕ}
    (h : src ∈ D.toDomainChain.transportRawArgsPart l) :
    ∀ y ∈ src, y ∈ (D.stageAt (D.argStage l)).domain :=
  D.toDomainChain.mem_domainAt_of_mem_transportRawArgsPart h

/-- The coordinate form of the traversal, with both index bounds explicit so no cast appears. -/
theorem transported_get {l src : List ℕ}
    (h : src ∈ D.toDomainChain.transportRawArgsPart l) {n : ℕ} (h₁ : n < l.length)
    (h₂ : n < src.length) :
    src.get ⟨n, h₂⟩ ∈ D.toDomainChain.transportTo (D.toDomainChain.rawRep (l.get ⟨n, h₁⟩)).1
      (D.argStage l) (D.toDomainChain.rawRep (l.get ⟨n, h₁⟩)).2 :=
  (D.toDomainChain.mem_transportRawArgsPart_iff.1 h).get h₁ h₂

/-! ### Reassembly

Both pipelines reassemble application data at the common stage. The two lemmas needed are that the
assembly succeeds and that it returns the transported list unchanged. -/

omit [L.EffectiveLanguage] in
private theorem argsList_funSymbolArgs {p : L.FunctionSymbol × List ℕ}
    (h : p.2.length = p.1.arity) :
    (FunctionApplicationData.equivSubtype.symm ⟨p, h⟩ :
      FunctionApplicationData L ℕ).argsList = p.2 :=
  congrArg (fun z : { q : L.FunctionSymbol × List ℕ // q.2.length = q.1.arity } ↦ z.1.2)
    (FunctionApplicationData.equivSubtype.apply_symm_apply ⟨p, h⟩)

omit [L.EffectiveLanguage] in
private theorem argsList_relSymbolArgs {p : L.RelationSymbol × List ℕ}
    (h : p.2.length = p.1.arity) :
    (RelationApplicationData.equivSubtype.symm ⟨p, h⟩ :
      RelationApplicationData L ℕ).argsList = p.2 :=
  congrArg (fun z : { q : L.RelationSymbol × List ℕ // q.2.length = q.1.arity } ↦ z.1.2)
    (RelationApplicationData.equivSubtype.apply_symm_apply ⟨p, h⟩)

theorem exists_funData_of_transported {d : FunctionApplicationData L ℕ} {src : List ℕ}
    (h : src ∈ D.toDomainChain.transportRawArgsPart d.argsList) :
    ∃ hlen : src.length = (d.toSymbol).arity,
      FunctionApplicationData.ofSymbolArgs? (d.toSymbol, src) =
        Option.some (FunctionApplicationData.equivSubtype.symm ⟨(d.toSymbol, src), hlen⟩) := by
  have hlen : src.length = (d.toSymbol).arity := by
    rw [transported_length h, FunctionApplicationData.argsList, List.length_ofFn]
    rfl
  exact ⟨hlen, FunctionApplicationData.ofSymbolArgs?_of_length_eq _ hlen⟩

theorem exists_relData_of_transported {d : RelationApplicationData L ℕ} {src : List ℕ}
    (h : src ∈ D.toDomainChain.transportRawArgsPart d.argsList) :
    ∃ hlen : src.length = (d.toSymbol).arity,
      RelationApplicationData.ofSymbolArgs? (d.toSymbol, src) =
        Option.some (RelationApplicationData.equivSubtype.symm ⟨(d.toSymbol, src), hlen⟩) := by
  have hlen : src.length = (d.toSymbol).arity := by
    rw [transported_length h, RelationApplicationData.argsList, List.length_ofFn]
    rfl
  exact ⟨hlen, RelationApplicationData.ofSymbolArgs?_of_length_eq _ hlen⟩

/-- The reassembled data's arguments are exactly the transported values, hence all in the common
stage — which is what makes the stage evaluator halt. -/
theorem funData_args_mem_stage {d : FunctionApplicationData L ℕ} {src : List ℕ}
    (hsrc : src ∈ D.toDomainChain.transportRawArgsPart d.argsList)
    {hlen : src.length = (d.toSymbol).arity} :
    ∀ k, (FunctionApplicationData.equivSubtype.symm ⟨(d.toSymbol, src), hlen⟩ :
        FunctionApplicationData L ℕ).args k ∈ (D.stageAt (D.argStage d.argsList)).domain := by
  intro k
  exact transported_mem_stage hsrc _ (List.get_mem _ _)

theorem relData_args_mem_stage {d : RelationApplicationData L ℕ} {src : List ℕ}
    (hsrc : src ∈ D.toDomainChain.transportRawArgsPart d.argsList)
    {hlen : src.length = (d.toSymbol).arity} :
    ∀ k, (RelationApplicationData.equivSubtype.symm ⟨(d.toSymbol, src), hlen⟩ :
        RelationApplicationData L ℕ).args k ∈ (D.stageAt (D.argStage d.argsList)).domain := by
  intro k
  exact transported_mem_stage hsrc _ (List.get_mem _ _)

/-! ### The named raw output

`(M, y)` is a valid representative. This one fact supplies both the halting of the final
canonicalization and the semantic theorem below. -/

theorem limMem_rawFunOutput {d : FunctionApplicationData L ℕ} {src : List ℕ}
    (hsrc : src ∈ D.toDomainChain.transportRawArgsPart d.argsList)
    {hlen : src.length = (d.toSymbol).arity} {y : ℕ}
    (hy : y ∈ (D.stageAt (D.argStage d.argsList)).funEval
      (FunctionApplicationData.equivSubtype.symm ⟨(d.toSymbol, src), hlen⟩)) :
    D.toDomainChain.limMem (D.argStage d.argsList, y) := by
  letI : L.Structure ℕ := (D.stageAt (D.argStage d.argsList)).str
  set d' : FunctionApplicationData L ℕ :=
    FunctionApplicationData.equivSubtype.symm ⟨(d.toSymbol, src), hlen⟩ with hd'
  have hargs := funData_args_mem_stage (D := D) hsrc (hlen := hlen)
  have hval : y = @FunctionApplicationData.funMap L ℕ
      (D.stageAt (D.argStage d.argsList)).str d' :=
    Part.mem_unique hy ((D.stageAt (D.argStage d.argsList)).funEval_correct d' hargs)
  rw [hval]
  exact (D.stageAt (D.argStage d.argsList)).domain_closed _ d'.symbol d'.args hargs

/-! ### Unconditional halting -/

theorem rawFunEvalPart_dom (d : FunctionApplicationData L ℕ) : (D.rawFunEvalPart d).Dom := by
  obtain ⟨src, hsrc⟩ :=
    Part.dom_iff_mem.1 (D.toDomainChain.transportRawArgsPart_dom d.argsList)
  obtain ⟨hlen, hd'⟩ := exists_funData_of_transported (D := D) hsrc
  set d' : FunctionApplicationData L ℕ :=
    FunctionApplicationData.equivSubtype.symm ⟨(d.toSymbol, src), hlen⟩ with hd'def
  have hy : @FunctionApplicationData.funMap L ℕ (D.stageAt (D.argStage d.argsList)).str d' ∈
      (D.stageAt (D.argStage d.argsList)).funEval d' :=
    (D.stageAt (D.argStage d.argsList)).funEval_correct d'
      (funData_args_mem_stage (D := D) hsrc (hlen := hlen))
  obtain ⟨c, hc⟩ := Part.dom_iff_mem.1
    (D.toDomainChain.canonicalPart_dom_of_limMem
      (limMem_rawFunOutput (D := D) hsrc (hlen := hlen) hy))
  exact Part.dom_iff_mem.2 ⟨c, mem_rawFunEvalPart_iff.2
    ⟨src, hsrc, d', by rw [hd']; rfl, _, hy, hc⟩⟩

theorem rawRelEvalPart_dom (d : RelationApplicationData L ℕ) : (D.rawRelEvalPart d).Dom := by
  obtain ⟨src, hsrc⟩ :=
    Part.dom_iff_mem.1 (D.toDomainChain.transportRawArgsPart_dom d.argsList)
  obtain ⟨hlen, hd'⟩ := exists_relData_of_transported (D := D) hsrc
  set d' : RelationApplicationData L ℕ :=
    RelationApplicationData.equivSubtype.symm ⟨(d.toSymbol, src), hlen⟩ with hd'def
  obtain ⟨b, hb, -⟩ := (D.stageAt (D.argStage d.argsList)).relEval_correct d'
    (relData_args_mem_stage (D := D) hsrc (hlen := hlen))
  exact Part.dom_iff_mem.2 ⟨b, mem_rawRelEvalPart_iff.2 ⟨src, hsrc, d', by rw [hd']; rfl, hb⟩⟩

/-! ### Returned function codes are accepted

Independent of any later carrier-closure theorem: the value comes out of `canonicalPart`, and
everything `canonicalPart` returns on a valid input is accepted. -/

theorem accepted_of_mem_rawFunEvalPart {d : FunctionApplicationData L ℕ} {c : ℕ}
    (hc : c ∈ D.rawFunEvalPart d) : D.toDomainChain.Accepted c := by
  obtain ⟨src, hsrc, d', hd', y, hy, hcan⟩ := mem_rawFunEvalPart_iff.1 hc
  obtain ⟨hlen, hd'eq⟩ := exists_funData_of_transported (D := D) hsrc
  rw [hd'eq, Option.mem_def, Option.some_inj] at hd'
  subst hd'
  exact D.toDomainChain.accepted_of_mem_canonicalPart
    (limMem_rawFunOutput (D := D) hsrc (hlen := hlen) hy) hcan

end CeStructureChainIn

end FirstOrder.Language
