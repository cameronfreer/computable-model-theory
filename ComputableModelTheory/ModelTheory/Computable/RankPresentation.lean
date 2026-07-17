/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.CePresentation

/-!
# The transported rank evaluators (Level-1 Pullback, computational core)

The factored partial evaluators of the rank presentation, defined **before** any
structure data so that all computational content is independent of off-domain choices:
each evaluator is the visible composition

1. partial traversal of `rankEnum` over the argument list (`listMapPart`),
2. the original partial evaluator on the reassembled source data,
3. `rankOf` on function outputs (relations return their verdict directly).

The reassembly goes through the guarded `ofSymbolArgs?`, which fails precisely on
length mismatch — impossible on-domain, harmless off-domain (the evaluators are
partial). `rankFunEval_spec` and `rankRelEval_spec` are the on-domain halting-and-value
specifications from which the rank structure's commuting squares follow; the structure
itself (`rankStr`, defined by defaulting these evaluators off-domain) and the bundled
Level-1 presentation come next.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

namespace CePresentationIn

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable (P : CePresentationIn O L)

/-- The transported function evaluator: traverse `rankEnum` over the arguments,
reassemble, run the original evaluator, and recode the output through `rankOf`. -/
noncomputable def rankFunEval : FunctionApplicationData L ℕ →. ℕ :=
  fun d ↦ (listMapPart P.rankEnum d.argsList).bind fun src ↦
    ((FunctionApplicationData.ofSymbolArgs? (d.toSymbol, src) : Option _) : Part _).bind
      fun d' ↦ (P.funEval d').bind P.rankOf

/-- The transported relation decider: traverse, reassemble, decide at the source. -/
noncomputable def rankRelEval : RelationApplicationData L ℕ →. Bool :=
  fun d ↦ (listMapPart P.rankEnum d.argsList).bind fun src ↦
    ((RelationApplicationData.ofSymbolArgs? (d.toSymbol, src) : Option _) : Part _).bind
      fun d' ↦ P.relEval d'

/-- The transported function evaluator is partial recursive in the oracle. -/
theorem rankFunEval_recursiveIn : RecursiveIn O P.rankFunEval := by
  have hA : RecursiveIn O fun d : FunctionApplicationData L ℕ ↦
      listMapPart P.rankEnum d.argsList :=
    (RecursiveIn.listMapPart P.rankEnum_recursiveIn).comp
      (FunctionApplicationData.primrec_argsList.to_comp.computableIn)
  have hAsm : RecursiveIn O fun p : FunctionApplicationData L ℕ × List ℕ ↦
      ((FunctionApplicationData.ofSymbolArgs? (p.1.toSymbol, p.2) :
        Option (FunctionApplicationData L ℕ)) : Part (FunctionApplicationData L ℕ)) :=
    ComputableIn.ofOption
      ((FunctionApplicationData.primrec_ofSymbolArgs?.to_comp.computableIn).comp
        (((FunctionApplicationData.primrec_toSymbol.to_comp.computableIn).comp
          ComputableIn.fst).pair ComputableIn.snd))
  have hEval : RecursiveIn O fun d' : FunctionApplicationData L ℕ ↦
      (P.funEval d').bind P.rankOf :=
    RecursiveIn.bind P.funEval_recursiveIn
      ((P.rankOf_recursiveIn.comp ComputableIn.snd).to₂)
  exact RecursiveIn.bind hA
    ((RecursiveIn.bind hAsm ((hEval.comp ComputableIn.snd).to₂)).to₂)

/-- The transported relation decider is partial recursive in the oracle. -/
theorem rankRelEval_recursiveIn : RecursiveIn O P.rankRelEval := by
  have hA : RecursiveIn O fun d : RelationApplicationData L ℕ ↦
      listMapPart P.rankEnum d.argsList :=
    (RecursiveIn.listMapPart P.rankEnum_recursiveIn).comp
      (RelationApplicationData.primrec_argsList.to_comp.computableIn)
  have hAsm : RecursiveIn O fun p : RelationApplicationData L ℕ × List ℕ ↦
      ((RelationApplicationData.ofSymbolArgs? (p.1.toSymbol, p.2) :
        Option (RelationApplicationData L ℕ)) : Part (RelationApplicationData L ℕ)) :=
    ComputableIn.ofOption
      ((RelationApplicationData.primrec_ofSymbolArgs?.to_comp.computableIn).comp
        (((RelationApplicationData.primrec_toSymbol.to_comp.computableIn).comp
          ComputableIn.fst).pair ComputableIn.snd))
  exact RecursiveIn.bind hA
    ((RecursiveIn.bind hAsm
      ((P.relEval_recursiveIn.comp ComputableIn.snd).to₂)).to₂)

/-- Elementwise traversal of the argument list, when every argument's rank is
realized: produces the source tuple in order. -/
private theorem argsList_traversal {arity : ℕ} (args : Fin arity → ℕ)
    (src : Fin arity → ℕ) (hsrc : ∀ k, src k ∈ P.rankEnum (args k)) :
    List.ofFn src ∈ listMapPart P.rankEnum (List.ofFn args) := by
  rw [mem_listMapPart_iff, List.forall₂_iff_get]
  refine ⟨by simp, ?_⟩
  intro i h₁ h₂
  simpa using hsrc ⟨i, by simpa using h₁⟩

/-- On-domain specification of the transported function evaluator: if every argument
rank is realized by a source element, the evaluator halts, and its value is a rank of
the source-side interpretation — the function half of the commuting square. -/
theorem rankFunEval_spec (d : FunctionApplicationData L ℕ)
    (src : Fin d.arity → ℕ) (hsrc : ∀ k, src k ∈ P.rankEnum (d.args k)) :
    ∃ y ∈ P.rankOf (@Structure.funMap L ℕ P.str d.arity d.symbol src),
      y ∈ P.rankFunEval d := by
  have hdom : ∀ k, src k ∈ P.domain :=
    fun k ↦ P.mem_domain_of_mem_rankEnum (hsrc k)
  have hlen : (List.ofFn src).length = d.toSymbol.arity := by
    simp [FunctionApplicationData.toSymbol, FunctionSymbol.arity]
  set d' : FunctionApplicationData L ℕ :=
    FunctionApplicationData.equivSubtype.symm ⟨(d.toSymbol, List.ofFn src), hlen⟩
    with hd'
  have hargs : d'.args = src := by
    funext i
    show (List.ofFn src).get (Fin.cast hlen.symm i) = src i
    simp
  have hd'args : ∀ k, d'.args k ∈ P.domain := fun k ↦ hargs ▸ hdom k
  have hfunMap : @FunctionApplicationData.funMap L ℕ P.str d' =
      @Structure.funMap L ℕ P.str d.arity d.symbol src := by
    show @Structure.funMap L ℕ P.str _ d'.symbol d'.args = _
    rw [hargs]
    exact rfl
  have hvalue := P.funEval_correct d' hd'args
  rw [hfunMap] at hvalue
  have hout : @Structure.funMap L ℕ P.str d.arity d.symbol src ∈ P.domain := by
    refine P.domain_closed _ d.symbol src fun k ↦ hdom k
  obtain ⟨y, hy⟩ := Part.dom_iff_mem.1 ((P.rankOf_dom_iff _).2 hout)
  refine ⟨y, hy, ?_⟩
  rw [rankFunEval]
  refine Part.mem_bind_iff.2 ⟨List.ofFn src, P.argsList_traversal d.args src hsrc, ?_⟩
  refine Part.mem_bind_iff.2 ⟨d', ?_, Part.mem_bind_iff.2 ⟨_, hvalue, hy⟩⟩
  rw [FunctionApplicationData.ofSymbolArgs?_of_length_eq _ hlen]
  exact Part.mem_some _

/-- On-domain specification of the transported relation decider: it halts with a
verdict equivalent to the source-side relation — the relation half of the commuting
square. -/
theorem rankRelEval_spec (d : RelationApplicationData L ℕ)
    (src : Fin d.arity → ℕ) (hsrc : ∀ k, src k ∈ P.rankEnum (d.args k)) :
    ∃ b ∈ P.rankRelEval d,
      (b = true ↔ @Structure.RelMap L ℕ P.str d.arity d.symbol src) := by
  have hdom : ∀ k, src k ∈ P.domain :=
    fun k ↦ P.mem_domain_of_mem_rankEnum (hsrc k)
  have hlen : (List.ofFn src).length = d.toSymbol.arity := by
    simp [RelationApplicationData.toSymbol, RelationSymbol.arity]
  set d' : RelationApplicationData L ℕ :=
    RelationApplicationData.equivSubtype.symm ⟨(d.toSymbol, List.ofFn src), hlen⟩
    with hd'
  have hargs : d'.args = src := by
    funext i
    show (List.ofFn src).get (Fin.cast hlen.symm i) = src i
    simp
  have hd'args : ∀ k, d'.args k ∈ P.domain := fun k ↦ hargs ▸ hdom k
  have hrelMap : @RelationApplicationData.relMap L ℕ P.str d' ↔
      @Structure.RelMap L ℕ P.str d.arity d.symbol src := by
    show @Structure.RelMap L ℕ P.str _ d'.symbol d'.args ↔ _
    rw [hargs]
    exact Iff.rfl
  obtain ⟨b, hb, hbiff⟩ := P.relEval_correct d' hd'args
  refine ⟨b, ?_, hbiff.trans hrelMap⟩
  rw [rankRelEval]
  refine Part.mem_bind_iff.2 ⟨List.ofFn src, P.argsList_traversal d.args src hsrc, ?_⟩
  refine Part.mem_bind_iff.2 ⟨d', ?_, hb⟩
  rw [RelationApplicationData.ofSymbolArgs?_of_length_eq _ hlen]
  exact Part.mem_some _

end CePresentationIn

end FirstOrder.Language
